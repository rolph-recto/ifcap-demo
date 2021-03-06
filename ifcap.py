#!/usr/bin/env python3

import z3

## AST

### Statements

class Declare:
  def __init__(self, var, init_val):
    self.var = var
    self.init_val = init_val

  def __str__(self):
    return str(self.var) + " := " + str(self.init_val)

# alias one ref to another
class Assign:
  def __init__(self, var, rhs):
    self.var = var
    self.rhs = rhs

  def __str__(self):
    return str(self.var) + " := " + str(self.rhs)

# write into a ref's contents
class Write:
  def __init__(self, var, rhs):
    self.var = var
    self.rhs = rhs

  def __str__(self):
    return str(self.var) + " := " + str(self.rhs)

class Fork:
  def __init__(self, handle, prog):
    self.handle = handle
    self.spawned_prog = prog

  def __str__(self):
    return self.handle + " <- fork { ... }"

class Join:
  def __init__(self, handle):
    self.handle = handle

  def __str__(self):
    return "join " + self.handle

class Send:
  def __init__(self, msg, chan):
    self.msg = msg
    self.chan = chan

  def __str__(self):
    return "send " + str(self.msg) + " to " + str(self.chan)

class Receive:
  def __init__(self, var, chan):
    self.var = var
    self.chan = chan

  def __str__(self):
    return str(self.var) + " <- recv from " + str(self.chan)

class Cond:
  def __init__(self, guard, thenBranch, elseBranch):
    self.guard = guard
    self.thenBranch = thenBranch
    self.elseBranch = elseBranch

  def __str__(self):
    return "if (" + str(self.guard) + ") { ... } else { ... }"

class While:
  def __init__(self, guard, body):
    self.guard
    self.body = body

  def __str__(self):
    return "while (" + str(self.guard) + ") { ... }"

class Block:
  def __init__(self, stmts):
    self.statements = stmts

  def add(self, stmt):
    self.statements.append(stmt)

  def __str__(self):
    return "\n".join(map(lambda s: str(s), self.statements))

### Expressions

class Read:
  def __init__(self, var):
    self.var = var

  def __str__(self):
    return self.var

class Literal:
  def __init__(self, v):
    self.value = v

  def __str__(self):
    return str(self.value)

class Binop:
  def __init__(self, lhs, rhs):
    self.lhs = lhs
    self.rhs = rhs

  def __str__(self):
    return str(self.lhs) + " * " + str(self.rhs)

class NewRef:
  def __init__(self, val):
    self.val = val

  def __str__(self):
    return "newref(" + str(self.val) + ")"

class NewChan:
  def __init__(self, val):
    self.val = val

  def __str__(self):
    return "newchan()"

class Deref:
  def __init__(self, ref):
    self.ref = ref

  def __str__(self):
    return "!" + str(self.ref)

## Type

class IntType:
  def __init__(self):
    pass

  def __eq__(self, other):
    return isinstance(other, IntType)

  def __str__(self):
    return "int"

  def __repr__(self):
    return self.__str__()

class RefType:
  def __init__(self, cell_type, label):
    self.cell_type = cell_type
    self.label = label

  def __eq__(self, other):
    return isinstance(other, RefType) and self.cell_type == other.cell_type

  def __str__(self):
    return "(" + str(self.cell_type) + ") ref"

  def __repr__(self):
    return self.__str__()

class ChanType:
  def __init__(self, cell_type, ref_label, chan_label):
    self.cell_type = cell_type
    self.ref_label = ref_label
    self.chan_label = chan_label

  def __eq__(self, other):
    return isinstance(other, ChanType) and self.cell_type == other.cell_type

  def __str__(self):
    return "(" + str(self.cell_type) + ") chan"

  def __repr__(self):
    return self.__str__()


## Solver

class TypeChecker:
  def __init__(self):
    self.solver = z3.Solver()
    self.reset()

  def reset(self):
    self.pc_count = 1
    self.ref_count = 1
    self.chan_count = 1
    self.assert_count = 1
    self.assert_map = dict()
    self.program_map = dict()
    self.solver.reset()

  def new_label(self, name):
    return z3.Function(name, z3.IntSort(), z3.BoolSort())

  def new_ref_label(self, prog):
    label = self.new_label(("ref" + str(self.ref_count)))
    self.constr_nonempty(label, prog)
    self.ref_count += 1
    return label

  def new_chan_label(self, prog):
    label = self.new_label(("chan" + str(self.chan_count)))
    self.constr_nonempty(label, prog)
    self.chan_count += 1
    return label

  def new_pc(self):
    pc = self.new_label(("pc" + str(self.pc_count)))
    self.pc_count += 1
    return pc

  def check(self, prog):
    self.reset()

    out_type_ctx, out_proc_ctx, out_pc = \
        self._check(dict(), dict(), self.new_pc(), prog)

    result = self.solver.check()
    unsat_core = self.solver.unsat_core()

    unsat_core_map = dict()
    for assert_name in self.assert_map:
      if z3.Bool(assert_name) in unsat_core:
        unsat_core_map[assert_name] = \
            (self.assert_map[assert_name], self.program_map[assert_name])

    return result == z3.sat, unsat_core_map


  ## constraints
  def add_assert(self, prop, prog):
    assert_name = "assert" + str(self.assert_count)
    self.assert_count += 1

    self.solver.assert_and_track(prop, assert_name)
    self.assert_map[assert_name] = prop
    self.program_map[assert_name] = prog

  # c1 forks off c2 and c3
  # c1 <= c2 \meet c3
  def constr_fork(self, c1, c2, c3, prog):
    x = z3.Int("x")
    self.add_assert(z3.ForAll([x], z3.Implies(z3.Or(c2(x), c3(x)), c1(x))), prog)

  # c1 and c2 join to c3
  # c1 \meet c3 <= c3
  def constr_join(self, c1, c2, c3, prog):
    x = z3.Int("x")
    self.add_assert(z3.ForAll([x], z3.Implies(c3(x), z3.Or(c1(x), c2(x)))), prog)

  # pc1 and pc2 have a control point join at pc3
  # pc1 \join pc2 <= p3
  def constr_control_join(self, pc1, pc2, pc3, prog):
    x = z3.Int("x")
    self.add_assert(z3.ForAll([x], z3.Implies(pc3(x), z3.And(pc1(x), pc2(x)))), prog)

  # two regions are disjoint
  def constr_disjoint(self, r1, r2, prog):
    x = z3.Int("x")
    self.add_assert(z3.ForAll([x], z3.Not(z3.And(r1(x), r2(x)))), prog)

  # ref r1 is aliased to ref r2
  # r1 <= r2
  def constr_subsume(self, r1, r2, prog):
    x = z3.Int("x")
    self.add_assert(z3.ForAll([x], z3.Implies(r2(x), r1(x))), prog)

  # process p writes to v
  # p <= v
  def constr_write(self, p, v, prog):
    x = z3.Int("x")
    self.add_assert(z3.ForAll([x], z3.Implies(v(x), p(x))), prog)

  # process p reads from v
  # p \join v != top
  def constr_read(self, p, v, prog):
    x = z3.Int("x")
    self.add_assert(z3.Exists([x], z3.And(p(x), v(x))), prog)

  # data region v is not empty
  def constr_nonempty(self, v, prog):
    x = z3.Int("x")
    self.add_assert(z3.Exists([x], v(x)), prog)


  ## type and context unification

  def unify_types(self, t1, t2, prog):
    if isinstance(t1, IntType) and isinstance(t2, IntType):
      return IntType()

    elif isinstance(t1, RefType) and isinstance(t2, RefType):
      if t1.label is not t2.label:
        unified_cell_type = self.unify_types(t1.cell_type, t2.cell_type, prog)
        unified_ref_label = self.new_ref_label(prog)

        self.constr_control_join(t1.label, t2.label, unified_ref_label, prog)

        return RefType(unified_cell_type, unified_ref_label)

      else:
        return t1

    elif isinstance(t1, ChanType) and isinstance(t2, ChanType):
      if t1.ref_label is not t2.ref_label or t1.chan_label is not t2.chan_label:
        unified_cell_type = self.unify_types(t1.cell_type, t2.cell_type, prog)

        unified_ref_label = None
        if t1.ref_label is not t2.ref_label:
          unified_ref_label = self.new_ref_label(prog)
          self.constr_control_join(t1.ref_label, t2.ref_label, \
              unified_ref_label, prog)

        else:
          unified_ref_label = t1.ref_label

        unified_chan_label = None
        if t1.chan_label is not t2.chan_label:
          unified_chan_label = self.new_chan_label(prog)
          self.constr_control_join(t1.chan_label, t2.chan_label, \
              unified_ref_label, prog)

        else:
          unified_chan_label = t1.chan_label

        return ChanType(unified_cell_type, unified_ref_label, unified_chan_label)

      else:
        return t1

    else:
      raise Exception("cannot unify types: " + str(t1) + " and " + str(t2))

  def unify_contexts(self, ctx1, ctx2, prog):
    unified_ctx = dict()

    for key in ctx1:
      if key in ctx2:
        unified_ctx[key] = \
            self.unify_types(ctx1[key], ctx2[key], prog)

    return unified_ctx


  ## the actual type checking algorithm!!

  def _checkExpr(self, type_ctx, pc, expr):
    if isinstance(expr, Read):
      return type_ctx[expr.var]

    elif isinstance(expr, Literal):
      return IntType()

    elif isinstance(expr, NewRef):
      cell_type = self._checkExpr(type_ctx, pc, expr.val)
      label = self.new_ref_label(expr)
      return RefType(cell_type, label)

    elif isinstance(expr, NewChan):
      cell_type = self._checkExpr(type_ctx, pc, expr.val)
      ref_label = self.new_ref_label(expr)
      chan_label = self.new_chan_label(expr)
      return ChanType(cell_type, ref_label, chan_label)

    elif isinstance(expr, Deref):
      ref_type = self._checkExpr(type_ctx, pc, expr.ref)

      assert(isinstance(ref_type, RefType))
      self.constr_read(pc, ref_type.label, expr)

      return ref_type.cell_type

    elif isinstance(expr, Binop):
      lhs_type = self._checkExpr(type_ctx, pc, expr.lhs)
      rhs_type = self._checkExpr(type_ctx, pc, expr.rhs)

      assert(isinstance(lhs_type, IntType) and isinstance(rhs_type, IntType))

      return IntType()

  def update_type(self, var, old_type, new_type):
    if isinstance(var, Read):
      return new_type

    elif isinstance(var, Deref) and isinstance(old_type, RefType):
      new_cell_type = self.update_type(var.ref, old_type.cell_type, new_type)
      return RefType(new_cell_type, old_type.label)

    else:
      raise Exception("cannot update type of lval " + str(var))

  def get_lval_var(self, lval):
    if isinstance(lval, Read):
      return lval.var

    elif isinstance(lval, Deref):
      return self.get_lval_var(lval.ref)

  def can_subsume(self, t1, t2, prog):
    if isinstance(t1, IntType) and isinstance(t2, IntType):
      return True

    elif isinstance(t1, RefType) and isinstance(t2, RefType):
      if self.can_subsume(t1.cell_type, t2.cell_type, prog):
        if t1.label is not t2.label:
          # covariance
          self.constr_subsume(t2.label, t1.label, prog)

          # contravariance
          self.constr_subsume(t1.label, t2.label, prog)

        return True

      else:
        return False

    elif isinstance(t1, ChanType) and isinstance(t2, ChanType):
      if self.can_subsume(t1.cell_type, t2.cell_type, prog):
        if t1.ref_label is not t2.ref_label:
          self.constr_subsume(t2.ref_label, t1.ref_label, prog)

        if t1.chan_label is not t2.chan_label:
          # TODO: should this be backwards?
          # intuition for why this should be right is that the channel region
          # can be bigger than is labeled, but it would be unsafe if the
          # channel region were *smaller* than is labeled
          self.constr_subsume(t2.chan_label, t1.chan_label, prog)

        return True

      else:
        return False

    else:
      return False

  def _check(self, type_ctx, proc_ctx, pc, prog):
    if isinstance(prog, Declare):
      init_type = self._checkExpr(type_ctx, pc, prog.init_val)
      out_type_ctx = dict(type_ctx)
      out_type_ctx[prog.var] = init_type
      return out_type_ctx, proc_ctx, pc

    elif isinstance(prog, Assign):
      var_type = self._checkExpr(type_ctx, pc, prog.var)
      rhs_type = self._checkExpr(type_ctx, pc, prog.rhs)

      assert(isinstance(var_type, RefType) and isinstance(rhs_type, RefType))
      assert(var_type.cell_type == rhs_type.cell_type)
      lval_var = self.get_lval_var(prog.var)
      new_type = self.update_type(prog.var, type_ctx[lval_var], rhs_type)
      out_type_ctx = dict(type_ctx)
      out_type_ctx[lval_var] = new_type

      return out_type_ctx, proc_ctx, pc

    elif isinstance(prog, Write):
      var_type = self._checkExpr(type_ctx, pc, prog.var)
      rhs_type = self._checkExpr(type_ctx, pc, prog.rhs)

      assert(isinstance(var_type, RefType))
      if self.can_subsume(var_type.cell_type, rhs_type, prog):
        self.constr_write(pc, var_type.label, prog)
        return type_ctx, proc_ctx, pc

      else:
        raise Exception("cannot subsume type " + str(var_type.cell_type) + \
            " to " + str(rhs_type))

    elif isinstance(prog, Fork):
      spawn_pc = self.new_pc()
      cont_pc = self.new_pc()

      self.constr_fork(pc, cont_pc, spawn_pc, prog)
      self.constr_disjoint(cont_pc, spawn_pc, prog)

      sout_type_ctx, sout_proc_ctx, sout_pc = \
          self._check(type_ctx, proc_ctx, spawn_pc, prog.spawned_prog)

      out_proc_ctx = dict(sout_proc_ctx)
      out_proc_ctx[prog.handle] = (sout_type_ctx, sout_pc)

      return type_ctx, out_proc_ctx, cont_pc

    elif isinstance(prog, Join):
      if prog.handle not in proc_ctx:
        raise Exception("no existing process handle: " + prog.handle)

      spawn_type_ctx, spawn_pc = proc_ctx[prog.handle]

      out_proc_ctx = dict()
      for handle, proc_ctx_pc in proc_ctx.items():
        if handle != prog.handle:
          out_proc_ctx[handle] = proc_ctx_pc

      out_pc = self.new_pc()
      self.constr_join(spawn_pc, pc, out_pc, prog)

      return type_ctx, out_proc_ctx, out_pc

    elif isinstance(prog, Send):
      msg_type = self._checkExpr(type_ctx, pc, prog.msg)
      chan_type = self._checkExpr(type_ctx, pc, prog.chan)

      if self.can_subsume(chan_type.cell_type, msg_type, prog):
        out_pc = self.new_pc()

        # can only give away capability that the pc currently has
        self.constr_write(pc, chan_type.chan_label, prog)

        # give away capability and store it in the channel label
        self.constr_fork(pc, chan_type.chan_label, out_pc, prog)
        self.constr_disjoint(chan_type.chan_label, out_pc, prog)

        return type_ctx, proc_ctx, out_pc

      else:
        raise Exception("cannot subsume type " + str(chan_type.cell_type) + \
            " to " + str(msg_type))

    elif isinstance(prog, Receive):
      chan_type = self._checkExpr(type_ctx, pc, prog.chan)

      # need write cap on receive to prevent recv contention
      self.constr_write(pc, chan_type.ref_label, prog)

      out_type_ctx = dict(type_ctx)
      out_type_ctx[prog.var] = chan_type.cell_type

      out_pc = self.new_pc()
      self.constr_join(pc, chan_type.chan_label, out_pc, prog)

      return out_type_ctx, proc_ctx, out_pc

    elif isinstance(prog, Cond):
      self._checkExpr(type_ctx, pc, prog.guard)

      tout_type_ctx, tout_proc_ctx, tout_pc = \
          self._check(type_ctx, proc_ctx, pc, prog.thenBranch)

      eout_type_ctx, eout_proc_ctx, eout_pc = \
          self._check(type_ctx, proc_ctx, pc, prog.elseBranch)

      out_type_ctx = self.unify_contexts(tout_type_ctx, eout_type_ctx, prog)

      out_pc = self.new_pc()
      self.constr_control_join(tout_pc, eout_pc, out_pc, prog)

      assert(tout_proc_ctx == eout_proc_ctx)

      return out_type_ctx, tout_proc_ctx, out_pc

    elif isinstance(prog, While):
      self._checkExpr(type_ctx, pc, prog.guard)
      bout_type_ctx, bout_proc_ctx, bout_pc = \
          self._check(type_ctx, dict(), pc, prog.body)

      out_type_ctx = self.unify_contexts(type_ctx, bout_type_ctx, prog)

      assert(bout_proc_ctx == dict())

      out_pc = self.new_pc()
      self.constr_control_join(pc, bout_pc, out_pc, prog)

      return out_type_ctx, proc_ctx, out_pc

    elif isinstance(prog, Block):
      cur_type_ctx = type_ctx
      cur_proc_ctx = proc_ctx
      cur_pc = pc

      for stmt in prog.statements:
        cur_type_ctx, cur_proc_ctx, cur_pc = \
          self._check(cur_type_ctx, cur_proc_ctx, cur_pc, stmt)

      return cur_type_ctx, cur_proc_ctx, cur_pc


def print_expr(expr):
  if isinstance(expr, Read):
    return expr.var

  elif isinstance(expr, Literal):
    return str(expr.value)

  elif isinstance(expr, Binop):
    return print_expr(expr.lhs) + " * " + print_expr(expr.rhs)

  elif isinstance(expr, NewRef):
    return "newref(" + print_expr(expr.val) + ")"

  elif isinstance(expr, NewChan):
    return "newchan()"

  elif isinstance(expr, Deref):
    return "!" + print_expr(expr.ref)

def print_stmt(prog, indent_level=0):
  indent = " " * indent_level

  if isinstance(prog, Declare):
    return indent + prog.var + " := " + print_expr(prog.init_val)

  elif isinstance(prog, Assign):
    return indent + print_expr(prog.var) + " = " + print_expr(prog.rhs)

  elif isinstance(prog, Write):
    return indent + print_expr(prog.var) + " := " + print_expr(prog.rhs)

  elif isinstance(prog, Fork):
    return indent + prog.handle + " <- fork {\n" + \
        print_stmt(prog.spawned_prog, indent_level+2) + "\n" + indent + "}"

  elif isinstance(prog, Join):
    return indent + "join " + prog.handle

  elif isinstance(prog, Send):
    return indent + "send " + print_expr(prog.msg) + " to " + print_expr(prog.chan)

  elif isinstance(prog, Receive):
    return indent + prog.var + " <- recv from " + print_expr(prog.chan)

  elif isinstance(prog, Cond):
    return indent + "if (" + print_expr(prog.guard) + ") {\n" + \
        print_stmt(prog.thenBranch, indent_level+2) + "\n" + indent + \
        "} else {\n" + \
        print_stmt(prog.elseBranch, indent_level+2) + "\n" + indent + "}"

  elif isinstance(prog, While):
    return indent + "while (" + print_expr(prog.guard) + ") {\n" + \
        print_stmt(prog.body, indent_level+2) + "\n" + indent + "}"

  elif isinstance(prog, Block):
    block_str_list = []

    for stmt in prog.statements:
      block_str_list.append(print_stmt(stmt, indent_level))

    return "\n".join(block_str_list)


# write-read race
prog1 = \
  Block([
    Declare("x", NewRef(Literal(0))),
    Declare("y", NewRef(Literal(0))),
    Fork("f", Block([
      Write(Read("y"), Deref(Read("x")))
    ])),
    Write(Read("x"), Literal(1)),
    Join("f"),
    Write(Read("x"), Literal(2))
  ])


# write-write race because of aliasing
prog2 = \
  Block([
    Declare("x", NewRef(Literal(0))),
    Declare("y", NewRef(Literal(0))),
    Assign(Read("y"), Read("x")),
    Fork("f", Block([
      Write(Read("y"), Literal(0))
    ])),
    Write(Read("x"), Literal(1)),
    Join("f"),
    Write(Read("x"), Literal(2))
  ])


# no races because we re-point y before writing to it in forked process!
prog3 = \
  Block([
    Declare("x", NewRef(Literal(0))),
    Declare("y", NewRef(Literal(0))),
    Assign(Read("y"), Read("x")),
    Fork("f", Block([
      Assign(Read("y"), NewRef(Literal(0))),
      Write(Read("y"), Literal(0))
    ])),
    Write(Read("x"), Literal(1)),
    Join("f"),
    Write(Read("x"), Literal(2))
  ])

# write-write race because of aliasing, with a branch
prog4 = \
  Block([
    Declare("x", NewRef(Literal(0))),
    Declare("y", NewRef(Literal(0))),
    Assign(Read("y"), Read("x")),
    Fork("f", Block([
      Cond(Literal(0),
        Write(Read("y"), Literal(0)),
        Block([])
      )
    ])),
    Write(Read("x"), Literal(1)),
    Join("f"),
    Write(Read("x"), Literal(2))
  ])

# no races (concurrent reads)
prog5 = \
  Block([
    Declare("x", NewRef(Literal(0))),
    Declare("y", NewRef(Literal(0))),
    Declare("z", NewRef(Literal(0))),
    Fork("f", Block([
      Write(Read("y"), Deref(Read("x")))
    ])),
    Write(Read("z"), Deref(Read("x"))),
    Join("f"),
    Write(Read("x"), Literal(2))
  ])

# write-write race with nested refs
prog6 = \
  Block([
    Declare("x", NewRef(Literal(0))),
    Declare("y", NewRef(NewRef(Literal(0)))),
    Assign(Deref(Read("y")), Read("x")),
    Fork("f", Block([
      Cond(Literal(0),
        Write(Deref(Read("y")), Literal(0)),
        Block([])
      )
    ])),
    Write(Read("x"), Literal(1)),
    Join("f"),
    Write(Read("x"), Literal(2))
  ])


## write-write race, multiple processes and conditionals
prog7 = \
  Block([
    Declare("x", NewRef(Literal(0))),
    Declare("y", NewRef(Literal(0))),
    Assign(Read("y"), Read("x")),
    Fork("f", Block([
      Cond(Literal(0),
        Write(Read("y"), Literal(0)),
        Block([])
      )
    ])),
    Fork("q", Block([
      Write(Read("x"), Literal(1))
    ])),
    Join("f"),
    Join("q")
  ])


## write-write race, multiple processes
prog8 = \
  Block([
    Declare("x", NewRef(Literal(0))),
    Declare("y", NewRef(Literal(0))),
    Assign(Read("y"), Read("x")),
    Fork("f", Block([])),
    Fork("q", Block([
      Write(Read("y"), Literal(1))
    ])),
    Join("f"),
    Write(Read("x"), Literal(2)),
    Join("q")
  ])


## write-write race, nested refs
prog9 = \
  Block([
    Declare("x", NewRef(Literal(0))),
    Declare("y", NewRef(NewRef(Literal(0)))),
    Declare("z", NewRef(NewRef(Literal(0)))),
    Assign(Deref(Read("y")), Read("x")),
    Assign(Deref(Read("z")), Read("x")),
    Fork("f", Block([])),
    Fork("q", Block([
      Write(Deref(Read("y")), Literal(1))
    ])),
    Join("f"),
    Write(Deref(Read("z")), Literal(2)),
    Join("q")
  ])


# write-write race, re-point inside a conditional
prog10 = \
  Block([ \
    Declare("x", NewRef(Literal(0))), \
    Declare("y", NewRef(Literal(0))), \
    Assign(Read("y"), Read("x")),
    Fork("f", Block([ \
      Cond(Literal(0),
        Assign(Read("y"), NewRef(Literal(0))),
        Write(Read("y"), Literal(0))
      )
    ])), \
    Write(Read("x"), Literal(1)), \
    Join("f"), \
    Write(Read("x"), Literal(2))
  ])

# write-write race, re-point inside a conditional
prog11 = \
  Block([
    Declare("x", NewRef(Literal(0))),
    Declare("y", NewRef(Literal(0))),
    Assign(Read("y"), Read("x")),
    Fork("f", Block([
      Cond(Literal(0),
        Assign(Read("y"), NewRef(Literal(0))),
        Block([]),
      ),
      Write(Read("y"), Literal(0))
    ])),
    Write(Read("x"), Literal(1)),
    Join("f"),
    Write(Read("x"), Literal(2))
  ])


# no races, even though all writes are to x!
prog12 = \
  Block([
    Declare("x", NewRef(Literal(0))),
    Declare("y", NewRef(Literal(0))),
    Declare("z", NewRef(Literal(0))),
    Fork("p", Block([
      Assign(Read("x"), Read("y")),
      Fork("q", Block([
        Assign(Read("x"), Read("z")),
        Write(Read("x"), Literal(1))
      ])),
      Write(Read("x"), Literal(2)),
      Join("q"),
      Write(Read("x"), Literal(3))
    ])),
    Write(Read("x"), Literal(1)),
    Join("p"),
    Write(Read("x"), Literal(2))
  ])


def print_check(checker, name, prog, has_races):
  result, unsat_core = checker.check(prog)
  if result != has_races:
    print("test " + name + " failed!")

    if result:
      print("type checker says program is race-free, but it has a race:")

    else:
      print("type checker says program has races, but it does not:")

    print("")
    print(print_stmt(prog))
    print("")
    print("unsat core:")
    for assert_name, (prop, prog) in unsat_core.items():
      print(assert_name +  ": " + str(prop))
      print("generated by program location: ")
      print(str(prog))
      print("")

    print("")

  else:
    print("test " + name + " passed!")


## no races, transfer cap for x using a channel
prog13 = \
  Block([
    Declare("x", NewRef(Literal(0))),
    Declare("c", NewChan(Literal(0))),
    Fork("p", Block([
      Write(Read("x"), Literal(1)),
      Send(Literal(0), Read("c"))
    ])),
    Fork("q", Block([
      Receive("v", Read("c")),
      Write(Read("x"), Literal(2))
    ])),
    Join("p"),
    Join("q")
  ])

## has race (recv contention)
prog14 = \
  Block([
    Declare("x", NewRef(Literal(0))),
    Declare("c", NewChan(Literal(0))),
    Fork("p", Block([
      Write(Read("x"), Literal(1)),
      Send(Literal(0), Read("c"))
    ])),
    Fork("q", Block([
      Receive("v", Read("c")),
      Write(Read("x"), Literal(2))
    ])),
    Fork("r", Block([
      Receive("v", Read("c")),
      Write(Read("x"), Literal(2))
    ])),
    Join("p"),
    Join("q"),
    Join("r")
  ])


## has race (alias through nested refs)
prog15 = \
  Block([
    Declare("x", NewRef(Literal(0))),
    Declare("y", NewRef(NewRef(Literal(0)))),
    Write(Read("y"), Read("x")),
    Fork("p", Block([
      Write(Deref(Read("y")), Literal(1))
    ])),
    Write(Read("x"), Literal(2)),
    Join("p")
  ])

## no race (pass ref into a channel, pass channel into a channel)
prog16 = \
  Block([
    Declare("x", NewRef(Literal(0))),
    Declare("c", NewChan(NewChan(NewRef(Literal(0))))),
    Fork("p", Block([
      Receive("c2", Read("c")),
      Receive("y", Read("c2")),
      Write(Read("y"), Literal(1))
    ])),
    Fork("q", Block([
      Write(Read("x"), Literal(2)),
      Declare("c2", NewChan(NewRef(Literal(0)))),
      Send(Read("c2"), Read("c")),
      Send(Read("x"), Read("c2"))
    ])),
    Join("p"),
    Join("q")
  ])


## write-write race (pass ref into a channel, pass channel into a channel)
prog17 = \
  Block([
    Declare("x", NewRef(Literal(0))),
    Declare("c", NewChan(NewChan(NewRef(Literal(0))))),
    Fork("p", Block([
      Receive("c2", Read("c")),
      Receive("y", Read("c2")),
      Write(Read("y"), Literal(1))
    ])),
    Fork("q", Block([
      Declare("c2", NewChan(NewRef(Literal(0)))),
      Send(Read("c2"), Read("c")),
      Send(Read("x"), Read("c2")),
      Write(Read("x"), Literal(2))
    ])),
    Join("p"),
    Join("q")
  ])

prog18 = \
  Block([
    Declare("c", NewChan(NewChan(Literal(0)))),
    Declare("c1", NewChan(Literal(0))),
    Declare("c2", NewChan(Literal(0))),
    Fork("p", Block([
      Send(Read("c1"), Read("c")),
      Send(Literal(0), Read("c1")),
    ])),
    Fork("q", Block([
      Send(Read("c2"), Read("c")),
      Send(Literal(1), Read("c2")),
    ])),
    Receive("c'", Read("c")),
    Receive("x", Read("c'")),
    Receive("y", Read("c'")),
  ])

prog19 = \
  Block([
    Declare("c", NewChan(Literal(0))),
    Fork("p", Block([
      Send(Literal(0), Read("c")),
    ])),
    Fork("q", Block([
      Send(Literal(1), Read("c")),
    ])),
    Receive("x", Read("c")),
  ])

prog20 = \
  Block([
    Declare("rc", NewRef(NewChan(Literal(0)))),
    Declare("c1", NewChan(Literal(0))),
    Declare("c2", NewChan(Literal(0))),
    Cond(Literal(0),
      Write(Read("rc"), Read("c1")),
      Write(Read("rc"), Read("c2")),
    ),
    Fork("p", Block([
      Send(Literal(0), Deref(Read("rc")))
    ])),
    Send(Literal(1), Read("c1"))
  ])

prog21 = \
  Block([
    Declare("r", NewRef(NewRef(Literal(0)))),
    Declare("r1", NewRef(Literal(1))),
    Declare("r2", NewRef(Literal(2))),
    Cond(Literal(0),
      Write(Read("r"), Read("r1")),
      Write(Read("r"), Read("r2")),
    ),
    Fork("p", Block([
      Write(Deref(Read("r")), Literal(0)),
    ])),
    Write(Read("r1"), Literal(1)),
  ])

# counterexample for ref covariance
prog22 = \
  Block([
    Declare("r", NewRef(NewRef(Literal(0)))),
    Declare("r1", NewRef(Literal(1))),
    Declare("r2", NewRef(Literal(2))),
    Cond(Literal(0),
      Write(Read("r"), Read("r1")),
      Write(Read("r"), Read("r2")),
    ),
    Fork("p", Block([
      Write(Deref(Read("r")), Literal(3)),
    ])),
    Declare("x", Deref(Read("r1")))
  ])

# counterexample for ref contravariance
prog23 = \
  Block([
    Declare("r", NewRef(NewRef(Literal(0)))),
    Declare("r1", NewRef(Literal(1))),
    Declare("r2", NewRef(Literal(2))),
    Cond(Literal(0),
      Write(Read("r"), Read("r1")),
      Write(Read("r"), Read("r2")),
    ),
    Fork("p", Block([
      Declare("x", Deref(Deref(Read("r"))))
    ])),
    Write(Read("r1"), Literal(4))
  ])

def main():
  checker = TypeChecker()

  print_check(checker, "prog1", prog1, False)
  print_check(checker, "prog2", prog2, False)
  print_check(checker, "prog3", prog3, True)
  print_check(checker, "prog4", prog4, False)
  print_check(checker, "prog5", prog5, True)
  print_check(checker, "prog6", prog6, False)
  print_check(checker, "prog7", prog7, False)
  print_check(checker, "prog8", prog8, False)
  print_check(checker, "prog9", prog9, False)
  print_check(checker, "prog10", prog10, False)
  print_check(checker, "prog11", prog11, False)
  print_check(checker, "prog12", prog12, True)
  print_check(checker, "prog13", prog13, True)
  print_check(checker, "prog14", prog14, False)
  print_check(checker, "prog15", prog15, False)
  print_check(checker, "prog16", prog16, True)
  print_check(checker, "prog17", prog17, False)
  print_check(checker, "prog18", prog18, False)
  print_check(checker, "prog19", prog19, False)
  print_check(checker, "prog20", prog20, False)
  print_check(checker, "prog21", prog21, False)
  print_check(checker, "prog22", prog22, False)
  print_check(checker, "prog23", prog23, False)

