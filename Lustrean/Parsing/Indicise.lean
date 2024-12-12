import Lustrean.Parsing.Reify
import Lustrean.Parsing.Inline
import Misc

open Batteries (Vector)
open Lean hiding HashMap
open Meta Elab
open Std (HashMap)

-- Indicise phase.  This is responsible for resolving all the variable names, and replace them
-- with indices in the local context.  This is akin to a de Bruijn transformation, except that it
-- must take into account the fact that all the bindings are mutually recursive.

namespace Lustrean.Parsing
namespace Indicise
  inductive VarRef (n m : Nat) where
    | input_var (k : Fin n)
    | bound_var (k : Fin m)
    deriving Repr

  mutual
    inductive Expr (n m : Nat) where
      | interval (lb : &LowerBound) (up : &UpperBound)
      | var (k : &VarRef n m)
      | mon_op (op : MonOp) (e : &Expr n m)
      | bin_op (op : Reify.BinOp) (left right : &Expr n m)
      | ite (cond : &BoolExpr n m) (tb : &Expr n m) (eb : &Expr n m)
      deriving Repr, Inhabited

    inductive BoolExpr (n m : Nat) where
      | cmp_op (op : CmpOp) (left right : &Expr n m)
      | bin_op (op : BoolBinOp) (left right : &BoolExpr n m)
      deriving Repr, Inhabited
  end
  /-- A local variable in a node, that is, a variable that is only available in the local scope.
      This can be either an input variable, or a locally bound variable.  -/
  structure Var where
    name : &Name
    deriving Repr, Inhabited

  /-- A locally bound variable.  This is a local variable that is bound to a value -/
  structure BoundVar (n m : Nat) extends Var where
    value : &Expr n m
    deriving Repr, Inhabited

  mutual
    variable {n m : Nat} (input_vars : Vector Var n) (bound_vars : Vector (BoundVar n m) m)

    def Expr.toString : Expr n m → String
      | .interval lb up => s!"[{lb}, {up}]"
      | .var ⟨.input_var k, _⟩ => input_vars[k].name.toString
      | .var ⟨.bound_var k, _⟩ => bound_vars[k].name.toString
      | .mon_op op ⟨e, _⟩ => s!"({op} {e.toString})"
      | .bin_op op ⟨l, _⟩ ⟨r, _⟩ => s!"({op} {l.toString} {r.toString})"
      | .ite ⟨cond, _⟩ ⟨tb, _⟩ ⟨eb, _⟩ => s!"(if {cond.toString} {tb.toString} {eb.toString})"

    def BoolExpr.toString : BoolExpr n m → String
      | .cmp_op op ⟨left, _⟩ ⟨right, _⟩
      | .bin_op op ⟨left, _⟩ ⟨right, _⟩ => s!"({op} {left.toString} {right.toString})"
  end

  structure Node where
    name : Name
    n : Nat
    m : Nat
    input_vars : Vector Var n
    bound_vars : Vector (BoundVar n m) m
    output_vars : Array (VarRef n m)
    guards : Array (&BoolExpr n m)
    asserts : Array (&BoolExpr n m)
    deriving Repr, Inhabited

  namespace Node
    protected def getElem {n m} (nod : Node) (vr : VarRef n m) (p : n = nod.n ∧ m = nod.m) : Var :=
      match vr with
      | .input_var k => nod.input_vars[k]
      | .bound_var k => nod.bound_vars[k].toVar

    instance (n m : Nat) : GetElem Node (VarRef n m) Var fun nod _ => n = nod.n ∧ m = nod.m where
      getElem := Node.getElem

    protected def toString (self : Node) : String :=
      let args := ", ".intercalate <| self.input_vars.map (·.name.toString) |>.toList
      let outputs :=
        if self.output_vars.size > 0 then
          " = " ++ (", ".intercalate <| self.output_vars.map (self[·].name.toString) |>.toList)
        else
          ""
      let guards :=
        "guards" ++ (self.guards.map (fun b => s!"\n  {b.value.toString self.input_vars self.bound_vars}") |>.toList |> String.join)
      let asserts :=
        "asserts" ++ (self.asserts.map (fun b => s!"\n  {b.value.toString self.input_vars self.bound_vars}") |>.toList |> String.join)
      let vars :=
        "where" ++ (self.bound_vars.map (fun v =>
            s!"\n  {v.name.toString} = {v.value.value.toString self.input_vars self.bound_vars}")
          |>.toList
          |> String.join)
      s!"node {self.name}({args}){outputs}\n{guards}\n{vars}\n{asserts}"

    instance : ToString Node where
      toString := Node.toString
  end Node

  section
  variable {n m : Nat}
  variable (local_vars : HashMap Name (VarRef n m))

  mutual
    partial def elab_expr (e : &Inline.Expr) : CoreM (&Expr n m) :=
      e.mapM fun
        | .interval lb up => return .interval lb up
        | .var ⟨name, ref⟩ => do
          let some k := local_vars.get? name | throwErrorAt ref "unbound variable"
          return .var ⟨k, ref⟩
        | .mon_op op e => do
          let e ← elab_expr e
          return .mon_op op e
        | .bin_op op left right => do
          let left ← elab_expr left
          let right ← elab_expr right
          return .bin_op op left right
        | .ite cond tb eb => do
          let cond ← elab_boolexpr cond
          let tb ← elab_expr tb
          let eb ← elab_expr eb
          return .ite cond tb eb

    partial def elab_boolexpr (b : &Inline.BoolExpr) : CoreM (&BoolExpr n m) :=
      b.mapM fun
        | .cmp_op op left right => do
          let left ← elab_expr left
          let right ← elab_expr right
          return .cmp_op op left right
        | .bin_op op left right => do
          let left ← elab_boolexpr left
          let right ← elab_boolexpr right
          return .bin_op op left right
  end
  end

  def elab_node (nod : &Inline.Node) : CoreM (&Node) := nod.mapM fun nod => do
    let input_vars := Vector.mk nod.input_vars rfl
    let bound_vars := Vector.mk nod.bound_vars rfl
    let n := input_vars.size
    let m := bound_vars.size
    let mut env : HashMap Name (VarRef n m) := {}
    for h : i in [0:n] do
      env := env.insert input_vars[i].name <| .input_var ⟨i, Membership.get_elem_helper h rfl⟩
    for h : i in [0:m] do
      env := env.insert bound_vars[i].name <| .bound_var ⟨i, Membership.get_elem_helper h rfl⟩
    let input_vars := input_vars.map fun { name, } => { name }
    let bound_vars ← bound_vars.mapM fun var => do
      let { name, value } := var
      let value ← elab_expr env value
      return { name, value }
    let output_vars ← nod.output_vars.mapM (m := CoreM) fun var : &Name => do
      let some i := env.get? var | throwErrorAt var.ref "unbound variable"
      return i
    let guards ← nod.guards.mapM <| elab_boolexpr env
    let asserts ← nod.asserts.mapM <| elab_boolexpr env
    return { name := nod.name, n, input_vars, bound_vars, guards, asserts, output_vars }

  def elab_lustre (nodes : Array (&Inline.Node)) : CoreM (Array (&Node)) :=
    nodes.mapM elab_node
end Indicise

end Lustrean.Parsing
