#!/usr/bin/env python3

import z3

## AST

### Statements
class Declare:
  def __init__(self, var):
    self.var = var

class Assign:
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

class VarRead:
  def __init__(self, var):
    self.var = var

class Literal:
  def __init__(self, v):
    self.value = v

class Binop:
  def __init__(self, lhs, rhs):
    self.lhs = lhs
    self.rhs = rhs


### solver

TYPE_EXPR = 0
TYPE_STMT = 1

class TypeChecker:
  def __init__(self):
    self.solver = z3.Solver()
    self.pc_count = 0

  def new_label(self, name):
    return z3.Function(name, z3.IntSort(), z3.BoolSort())

  def new_pc(self):
    pc = self.new_label("pc" + str(self.pc_count))
    self.pc_count += 1
    return pc

  def check(self, prog):
    self.pc_count = 0
    self.solver.reset()

    out_type_ctx, out_proc_ctx, out_pc = \
        self._check(dict(), dict(), self.new_pc(), prog)

    return self.solver.check()

  # c1 forks off c2 and c3
  # c1 <= c2 \meet c3
  def constr_fork(self, c1, c2, c3):
    x = z3.Int("x")
    self.solver.add(\
        z3.ForAll([x], \
        z3.Implies( \
          z3.Or(c2(x), c3(x)), \
          c1(x))))


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


  def _checkExpr(self, type_ctx, pc, expr):
    if isinstance(expr, VarRead):
      self.constr_read(pc, type_ctx[expr.var])

    elif isinstance(expr, Literal):
      pass

    elif isinstance(expr, Binop):
      self._checkExpr(type_ctx, pc, expr.lhs)
      self._checkExpr(type_ctx, pc, expr.rhs)

  def _check(self, type_ctx, proc_ctx, pc, prog):
    if isinstance(prog, Declare):
      label = self.new_label(prog.var)
      self.constr_nonempty(label)

      out_type_ctx = dict(type_ctx)
      out_type_ctx[prog.var] = label
      return out_type_ctx, proc_ctx, pc

    elif isinstance(prog, Assign):
      self._checkExpr(type_ctx, pc, prog.rhs)
      self.constr_write(pc, type_ctx[prog.var])
      return type_ctx, proc_ctx, pc

    elif isinstance(prog, Fork):
      spawn_pc = self.new_pc()
      cont_pc = self.new_pc()

      self.constr_fork(pc, cont_pc, spawn_pc)
      self.constr_disjoint(cont_pc, spawn_pc)

      sout_type_ctx, sout_proc_ctx, sout_pc = \
          self._check(type_ctx, proc_ctx, spawn_pc, prog.spawned_prog)

      out_proc_ctx = dict(sout_proc_ctx)
      out_proc_ctx[prog.handle] = sout_pc

      return type_ctx, out_proc_ctx, cont_pc

    elif isinstance(prog, Join):
      if prog.handle not in proc_ctx:
        raise ("no existing process handle: " + prog.handle)

      fork_pc = proc_ctx[prog.handle]
      out_pc = self.new_pc()

      self.constr_join(fork_pc, pc, out_pc)
      return type_ctx, proc_ctx, out_pc

    elif isinstance(prog, Cond):
      self._checkExpr(type_ctx, pc, prog.guard)

      tout_type_ctx, tout_proc_ctx, tout_pc = \
          self._check(type_ctx, proc_ctx, pc, prog.thenBranch)

      eout_type_ctx, eout_proc_ctx, eout_pc = \
          self._check(type_ctx, proc_ctx, pc, prog.elseBranch)

      out_pc = self.new_pc()
      self.constr_control_join(tout_pc, eout_pc, out_pc)

      assert(tout_proc_ctx == eout_proc_ctx)

      return type_ctx, tout_proc_ctx, out_pc

    elif isinstance(prog, While):
      self._checkExpr(type_ctx, pc, prog.guard)
      bout_type_ctx, bout_proc_ctx, bout_pc = \
          self._check(type_ctx, dict(), pc, prog.body)

      assert(bout_proc_ctx == dict())

      out_pc = self.new_pc()
      self.constr_control_join(pc, bout_pc, out_pc)
      return type_ctx, proc_ctx, out_pc

    elif isinstance(prog, Block):
      cur_type_ctx = type_ctx
      cur_proc_ctx = proc_ctx
      cur_pc = pc

      for stmt in prog.statements:
        cur_type_ctx, cur_proc_ctx, cur_pc = \
          self._check(cur_type_ctx, cur_proc_ctx, cur_pc, stmt)

      return cur_type_ctx, cur_proc_ctx, cur_pc


def prog():
  return \
    Block([ \
      Declare("x"), \
      Declare("y"), \
      Fork("f", Block([ \
        Assign("y", VarRead("x"))
      ])), \
      Assign("x", Literal(1)), \
      Join("f"), \
      Assign("x", Literal(2))
    ])

def main():
  checker = TypeChecker()
  print(checker.check(prog()))

