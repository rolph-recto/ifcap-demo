#!/usr/bin/env python3

import z3

## AST

### Statements

class Declare:
  def __init__(self, var, init_val):
    self.var = var
    self.init_val = init_val

# alias one ref to another
class Assign:
  def __init__(self, var, rhs):
    self.var = var
    self.rhs = rhs

# write into a ref's contents
class Write:
  def __init__(self, var, rhs):
    self.var = var
    self.rhs = rhs

class Fork:
  def __init__(self, handle, prog):
    self.handle = handle
    self.spawned_prog = prog

class Join:
  def __init__(self, handle):
    self.handle = handle

class Cond:
  def __init__(self, guard, thenBranch, elseBranch):
    self.guard = guard
    self.thenBranch = thenBranch
    self.elseBranch = elseBranch

class While:
  def __init__(self, guard, body):
    self.guard
    self.body = body

class Block:
  def __init__(self, stmts):
    self.statements = stmts

  def add(self, stmt):
    self.statements.append(stmt)


### Expressions

class Read:
  def __init__(self, var):
    self.var = var

class Literal:
  def __init__(self, v):
    self.value = v

class Binop:
  def __init__(self, lhs, rhs):
    self.lhs = lhs
    self.rhs = rhs

class NewRef:
  def __init__(self, val):
    self.val = val

class Deref:
  def __init__(self, ref):
    self.ref = ref


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


## Solver

class TypeChecker:
  def __init__(self):
    self.solver = z3.Solver()
    self.pc_count = 1
    self.ref_count = 1

  def new_label(self, name):
    return z3.Function(name, z3.IntSort(), z3.BoolSort())

  def new_ref_label(self):
    label = self.new_label(("ref" + str(self.ref_count)))
    self.ref_count += 1
    return label

  def new_pc(self):
    pc = self.new_label(("pc" + str(self.pc_count)))
    self.pc_count += 1
    return pc

  def check(self, prog):
    self.pc_count = 0
    self.solver.reset()

    out_type_ctx, out_proc_ctx, out_pc = \
        self._check(dict(), dict(), self.new_pc(), prog)

    return self.solver.check() == z3.sat


  ## constraints

  # c1 forks off c2 and c3
  # c1 <= c2 \meet c3
  def constr_fork(self, c1, c2, c3):
    x = z3.Int("x")
    self.solver.add(z3.ForAll([x], z3.Implies(z3.Or(c2(x), c3(x)), c1(x))))

  # c1 and c2 join to c3
  # c1 \meet c3 <= c3
  def constr_join(self, c1, c2, c3):
    x = z3.Int("x")
    self.solver.add(z3.ForAll([x], z3.Implies(c3(x), z3.Or(c1(x), c2(x)))))

  # pc1 and pc2 have a control point join at pc3
  # pc1 \join pc2 <= p3
  def constr_control_join(self, pc1, pc2, pc3):
    x = z3.Int("x")
    self.solver.add(z3.ForAll([x], z3.Implies(pc3(x), z3.And(pc1(x), pc2(x)))))

  # two regions are disjoint
  def constr_disjoint(self, r1, r2):
    x = z3.Int("x")
    self.solver.add(z3.ForAll([x], z3.Not(z3.And(r1(x), r2(x)))))

  # ref r1 is aliased to ref r2
  # r1 <= r2
  def constr_alias(self, r1, r2):
    x = z3.Int("x")
    self.solver.add(z3.ForAll([x], z3.Implies(r2(x), r1(x))))

  # process p writes to v
  # p <= v
  def constr_write(self, p, v):
    x = z3.Int("x")
    self.solver.add(z3.ForAll([x], z3.Implies(v(x), p(x))))

  # process p reads from v
  # p \join v != top
  def constr_read(self, p, v):
    x = z3.Int("x")
    self.solver.add(z3.Exists([x], z3.And(p(x), v(x))))

  # data region v is not empty
  def constr_nonempty(self, v):
    x = z3.Int("x")
    self.solver.add(z3.Exists([x], v(x)))


  ## type and context unification

  def unify_types(self, t1, t2):
    if isinstance(t1, IntType) and isinstance(t2, IntType):
      return IntType()

    elif isinstance(t1, RefType) and isinstance(t2, RefType):
      if t1.label is not t2.label:
        unified_cell_type = self.unify_types(t1.cell_type, t2.cell_type)
        unified_ref_label = self.new_ref_label()
        self.constr_control_join(t1.label, t2.label, unified_ref_label)
        return RefType(unified_cell_type, unified_ref_label)

      else:
        return t1

  def unify_contexts(self, ctx1, ctx2):
    unified_ctx = dict()

    for key in ctx1:
      if key in ctx2:
        unified_ctx[key] = self.unify_types(ctx1[key], ctx2[key])

    return unified_ctx


  ## the actual type checking algorithm!!

  def _checkExpr(self, type_ctx, pc, expr):
    if isinstance(expr, Read):
      return type_ctx[expr.var]

    elif isinstance(expr, Literal):
      return IntType()

    elif isinstance(expr, NewRef):
      cell_type = self._checkExpr(type_ctx, pc, expr.val)
      label = self.new_ref_label()
      self.constr_nonempty(label)
      return RefType(cell_type, label)

    elif isinstance(expr, Deref):
      ref_type = self._checkExpr(type_ctx, pc, expr.ref)

      assert(isinstance(ref_type, RefType))
      self.constr_read(pc, ref_type.label)

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

      # self.constr_alias(var_type.label, rhs_type.label)
      lval_var = self.get_lval_var(prog.var)
      new_type = self.update_type(prog.var, type_ctx[lval_var], rhs_type)
      out_type_ctx = dict(type_ctx)
      out_type_ctx[lval_var] = new_type

      return out_type_ctx, proc_ctx, pc

    elif isinstance(prog, Write):
      var_type = self._checkExpr(type_ctx, pc, prog.var)
      rhs_type = self._checkExpr(type_ctx, pc, prog.rhs)

      assert(isinstance(var_type, RefType))
      assert(type(var_type.cell_type) == type(rhs_type))

      self.constr_write(pc, var_type.label)
      return type_ctx, proc_ctx, pc

    elif isinstance(prog, Fork):
      spawn_pc = self.new_pc()
      cont_pc = self.new_pc()

      self.constr_fork(pc, cont_pc, spawn_pc)
      self.constr_disjoint(cont_pc, spawn_pc)

      sout_type_ctx, sout_proc_ctx, sout_pc = \
          self._check(type_ctx, proc_ctx, spawn_pc, prog.spawned_prog)

      out_proc_ctx = dict(sout_proc_ctx)
      out_proc_ctx[prog.handle] = (sout_type_ctx, sout_pc)

      return type_ctx, out_proc_ctx, cont_pc

    elif isinstance(prog, Join):
      if prog.handle not in proc_ctx:
        raise ("no existing process handle: " + prog.handle)

      spawn_type_ctx, spawn_pc = proc_ctx[prog.handle]

      out_pc = self.new_pc()
      self.constr_join(spawn_pc, pc, out_pc)

      out_type_ctx = self.unify_contexts(type_ctx, spawn_type_ctx)

      return out_type_ctx, proc_ctx, out_pc

    elif isinstance(prog, Cond):
      self._checkExpr(type_ctx, pc, prog.guard)

      tout_type_ctx, tout_proc_ctx, tout_pc = \
          self._check(type_ctx, proc_ctx, pc, prog.thenBranch)

      eout_type_ctx, eout_proc_ctx, eout_pc = \
          self._check(type_ctx, proc_ctx, pc, prog.elseBranch)

      out_type_ctx = self.unify_contexts(tout_type_ctx, eout_type_ctx)

      out_pc = self.new_pc()
      self.constr_control_join(tout_pc, eout_pc, out_pc)

      assert(tout_proc_ctx == eout_proc_ctx)

      return out_type_ctx, tout_proc_ctx, out_pc

    elif isinstance(prog, While):
      self._checkExpr(type_ctx, pc, prog.guard)
      bout_type_ctx, bout_proc_ctx, bout_pc = \
          self._check(type_ctx, dict(), pc, prog.body)

      out_type_ctx = self.unify_contexts(type_ctx, bout_type_ctx)

      assert(bout_proc_ctx == dict())

      out_pc = self.new_pc()
      self.constr_control_join(pc, bout_pc, out_pc)

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

  elif isinstance(prog, Cond):
    return indent + "if (" + print_expr(prog.guard) + ") {\n" + \
        print_stmt(prog.thenBranch, indent_level+2) + "\n" + indent + \
        "} else {\n" + \
        print_stmt(prog.elseBranch, indent_level+2) + indent + "}"

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
  Block([ \
    Declare("x", NewRef(Literal(0))), \
    Declare("y", NewRef(Literal(0))), \
    Fork("f", Block([ \
      Write(Read("y"), Deref(Read("x")))
    ])), \
    Write(Read("x"), Literal(1)), \
    Join("f"), \
    Write(Read("x"), Literal(2))
  ])


# write-write race because of aliasing
prog2 = \
  Block([ \
    Declare("x", NewRef(Literal(0))), \
    Declare("y", NewRef(Literal(0))), \
    Assign(Read("y"), Read("x")),
    Fork("f", Block([ \
      Write(Read("y"), Literal(0))
    ])), \
    Write(Read("x"), Literal(1)), \
    Join("f"), \
    Write(Read("x"), Literal(2))
  ])


# no races because we re-point y before writing to it in forked process!
prog3 = \
  Block([ \
    Declare("x", NewRef(Literal(0))), \
    Declare("y", NewRef(Literal(0))), \
    Assign(Read("y"), Read("x")),
    Fork("f", Block([ \
      Assign(Read("y"), NewRef(Literal(0))),
      Write(Read("y"), Literal(0))
    ])), \
    Write(Read("x"), Literal(1)), \
    Join("f"), \
    Write(Read("x"), Literal(2))
  ])

# write-write race because of aliasing, with a branch
prog4 = \
  Block([ \
    Declare("x", NewRef(Literal(0))), \
    Declare("y", NewRef(Literal(0))), \
    Assign(Read("y"), Read("x")),
    Fork("f", Block([ \
      Cond(Literal(0), \
        Write(Read("y"), Literal(0)), \
        Block([]) \
      )
    ])), \
    Write(Read("x"), Literal(1)), \
    Join("f"), \
    Write(Read("x"), Literal(2))
  ])

# no races (concurrent reads)
prog5 = \
  Block([ \
    Declare("x", NewRef(Literal(0))), \
    Declare("y", NewRef(Literal(0))), \
    Declare("z", NewRef(Literal(0))), \
    Fork("f", Block([ \
      Write(Read("y"), Deref(Read("x")))
    ])), \
    Write(Read("z"), Deref(Read("x"))),
    Join("f"), \
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
      Write(Read("x"), Literal(1))
    ])),
    Join("f"),
    Write(Read("x"), Literal(2)),
    Join("q")
  ])


def print_check(checker, prog):
  print("")
  print(print_stmt(prog))
  print("race-free!" if checker.check(prog) else "has races!")

def main():
  checker = TypeChecker()

  print_check(checker, prog1)
  print_check(checker, prog2)
  print_check(checker, prog3)
  print_check(checker, prog4)
  print_check(checker, prog5)
  print_check(checker, prog6)
  print_check(checker, prog7)
  print_check(checker, prog8)

