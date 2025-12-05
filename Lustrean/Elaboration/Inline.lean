import Lustrean.Elaboration.Reify
import Misc

open Batteries
open Lean Meta Elab
open Std (HashMap)
-- Inline phase.  This is responsible for removing node calls from the AST.

namespace Lustrean.Elaboration

namespace Inline
export Reify (Variable)

inductive Error where
  | undefined_node (nod : &Name)
  | arity_mismatch (nod : &Name) (expected : Nat) (got : Nat)
  | multiple_output_vars_in_expr (ref : Syntax) (nod : &Name) (nb_vars : Nat)
  | multiple_vars_for_simple_expr (ref : Syntax) (nb_vars : Nat)
  | unpacking_mismatch (ref : Syntax) (nod : &Name) (expected : Nat) (got : Nat)

def Error.as_exception : Error → Exception
  | undefined_node nod =>
    .error nod.ref m!"node call of undefined node '{nod.value}'"
  | arity_mismatch nod expected got =>
    .error nod.ref m!"node '{nod.value}' expects {expected} arguments, but was given {got}"
  | multiple_output_vars_in_expr ref nod nb_vars =>
    .error ref m!"node '{nod.value}' returns {nb_vars} values, so it must be unpacked"
  | multiple_vars_for_simple_expr ref nb_vars =>
    .error ref m!"cannot unpack into {nb_vars} values a simple expression"
  | unpacking_mismatch ref nod expected got =>
    .error ref m!"node '{nod.value}' returns {got} values, but {expected} are being unpacked"

mutual
inductive Expr where
  | interval (lb : &LowerBound) (up : &UpperBound)
  | var (name : &Name)
  | mon_op (op : MonOp) (e : &Expr)
  | bin_op (op : Reify.BinOp) (left right : &Expr)
  | ite (cond : &BoolExpr) (tb eb : &Expr)
  deriving Repr, Inhabited

inductive BoolExpr where
  | cmp_op (op : CmpOp) (left right : &Expr)
  | bin_op (op : BoolBinOp) (left right : &BoolExpr)
  deriving Repr, Inhabited
end

structure BoundVar extends Variable where
  value : &Expr
  deriving Repr, Inhabited

mutual
variable (pre₁ : Name)
def Expr.with_prefix : Expr → Expr
  | .interval lb up => .interval lb up
  | .var name => .var <| name.map (pre₁ ++ ·)
  | .mon_op op e => .mon_op op (e.map (·.with_prefix))
  | .bin_op op l r => .bin_op op (l.map (·.with_prefix)) (r.map (·.with_prefix))
  | .ite cond tb eb => .ite (cond.map (·.with_prefix)) (tb.map (·.with_prefix)) (eb.map (·.with_prefix))
termination_by e => sizeOf e

def BoolExpr.with_prefix : BoolExpr → BoolExpr
  | .cmp_op op l r => .cmp_op op (l.map (·.with_prefix)) (r.map (·.with_prefix))
  | .bin_op op l r => .bin_op op (l.map (·.with_prefix)) (r.map (·.with_prefix))
termination_by e => sizeOf e
end

structure Node where
  name : &Name
  input_vars : Array Variable
  bound_vars : Array BoundVar
  output_vars : Array (&Name)
  guards : Array (&BoolExpr)
  asserts : Array (&BoolExpr)
  deriving Repr, Inhabited

def NodeAddT := StateT Node

namespace NodeAddT
variable {m : Type _ → Type _} [Monad m]
variable {α β}

instance : Monad (NodeAddT m) :=
  inferInstanceAs (Monad (StateT _ _))
instance [LawfulMonad m] : LawfulMonad (NodeAddT m) :=
  inferInstanceAs (LawfulMonad (StateT _ _))
instance (ε) [MonadExceptOf ε m] : MonadExceptOf ε (NodeAddT m) :=
  inferInstanceAs (MonadExceptOf _ (StateT _ _))
instance : MonadLift m (NodeAddT m) :=
  inferInstanceAs (MonadLift m (StateT _ _))

def addVar (var : BoundVar) : NodeAddT m PUnit := do
  let nod ← StateT.get
  StateT.set { nod with bound_vars := nod.bound_vars.push var }

def addGuard (g : &BoolExpr) : NodeAddT m PUnit := do
  let nod ← StateT.get
  StateT.set { nod with guards := nod.guards.push g }

def addAssert (a : &BoolExpr) : NodeAddT m PUnit := do
  let nod ← StateT.get
  StateT.set { nod with asserts := nod.asserts.push a }
end NodeAddT

abbrev NodeAddM := NodeAddT Id

abbrev InlineM := NodeAddT <| Except Error

  namespace InlineM
  abbrev addVar (var : BoundVar) : InlineM PUnit :=
    NodeAddT.addVar var

  abbrev addGuard (g : &BoolExpr) : InlineM PUnit :=
    NodeAddT.addGuard g

  abbrev addAssert (a : &BoolExpr) : InlineM PUnit :=
    NodeAddT.addAssert a

  protected def run (name : &Name) (input_vars : Array Variable) (output_vars : Array (&Name))
                    (self : InlineM Unit) : Except Error Node := do
    let initial_node : Node := {
      name, input_vars, output_vars
      bound_vars := #[], guards := #[], asserts := #[]
    }
    let ((), nod) ← StateT.run self initial_node
    return nod
end InlineM
open InlineM

section
variable (env : HashMap Name Node)
include env

mutual
partial def elabExprAux (bounds : Option (Array (&Name))) (var_name : Name) (e : &Reify.Expr)
                          : CounterT InlineM (&Expr) :=
  e.mapM fun
    | .int lb up => do_bounds <| .interval lb up
    | .var n => do_bounds <| .var n
    | .mon_op op e => do
      let e ← elabExprAux none var_name e
      do_bounds <| .mon_op op e
    | .bin_op op l r => do
      let left ← elabExprAux none var_name l
      let right ← elabExprAux none var_name r
      do_bounds <| .bin_op op left right
    | .ite cond tb eb => do
      let cond ← elabBoolexprAux var_name cond
      let tb ← elabExprAux none var_name tb
      let eb ← elabExprAux none var_name eb
      do_bounds <| .ite cond tb eb
    | .node nod args => do
      let .some node_def := env.get? nod | throw <| .undefined_node nod
      let pre₁ := var_name.num (← CounterT.incr)
      for g in node_def.guards do
        addAssert <| g.map (·.with_prefix pre₁) -- here, we add the guards of the called node
                                                -- as an *assert* of the calling node
      for a in node_def.asserts do
        addAssert <| a.map (·.with_prefix pre₁)
      unless node_def.input_vars.size = args.size do
        throw <| .arity_mismatch nod node_def.input_vars.size args.size
      for (v, arg) in node_def.input_vars.zip args do
        let name := v.name.map (pre₁ ++ ·)
        let value ← elabExprAux none name arg
        addVar { name, value := value }
      for bvar in node_def.bound_vars do
        addVar {
          name := bvar.name.map (pre₁ ++ ·)
          value := bvar.value.map (·.with_prefix pre₁)
        }
      match bounds with
      | some vars =>
        unless vars.size = node_def.output_vars.size do
          throw <| .unpacking_mismatch e.ref node_def.name vars.size node_def.output_vars.size
        for (var, old_var) in vars.zip node_def.output_vars do
          addVar {
            name := var
            value := old_var.map (.var <| ⟨pre₁ ++ ·, old_var.ref⟩)
          }
        return default        -- This is a bit ugly, but this result will never be actually
                              -- used...
      | none =>
        if h : node_def.output_vars.size = 1 then
          return .var <| node_def.output_vars[0].map (pre₁ ++ ·)
        else
          throw <| .multiple_output_vars_in_expr e.ref nod node_def.output_vars.size
where
  do_bounds (e' : Expr) : CounterT InlineM (&Expr) := do
    if let some b := bounds then
      if h : b.size = 1 then
        addVar {
          name := b[0]
          value := .mk e' e.ref
        }
      else
        throw <| .multiple_vars_for_simple_expr e.ref b.size
    return ⟨e', e.ref⟩


partial def elabBoolexprAux (pre₁ : Name) (b : &Reify.BoolExpr) : InlineM (&BoolExpr) :=
  b.mapM fun
    | .bin_op op l r => do
      let left ← elabBoolexprAux pre₁ l
      let right ← elabBoolexprAux pre₁ r
      return .bin_op op left right
    | .cmp_op op l r => do
      let left ← elabExprAux none pre₁ l |>.run
      let right ← elabExprAux none pre₁ r |>.run
      return .cmp_op op left right
end

def elabExpr (bounds : Array (&Name)) (e : &Reify.Expr) : InlineM Unit := do
  let _ ← elabExprAux env bounds bounds[0]! e |>.run
  return ()

def elabBoolexpr (guards : Bool) (i : Nat) (b : &Reify.BoolExpr) : InlineM Unit := do
  let b ← elabBoolexprAux env ((if guards then `guards else `asserts) ++ (.num .anonymous i)) b
  if guards then
    addGuard b
  else
    addAssert b

def elabNode (nod : &Reify.Node) : Except Exception (&Node) :=
  nod.mapM fun nod => Except.mapError Error.as_exception <|
    InlineM.run nod.name nod.input_vars nod.output_vars do
      for { names, value } in nod.bound_vars do
        elabExpr env names value
      for (b, i) in nod.guards.zipIdx do
        elabBoolexpr env true i b
      for (b, i) in nod.asserts.zipIdx do
        elabBoolexpr env false i b
end

def elabLustre (nodes : Array (&Reify.Node)) : CoreM (Array (&Node)) := do
  let mut env := {}
  let mut result := Array.mkEmpty nodes.size
  for nod in nodes do
    let nod ← liftExcept <| elabNode env nod
    result := result.push nod
    env := env.insert nod.value.name nod
  return result

end Inline
end Lustrean.Elaboration
