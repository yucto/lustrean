import Lustrean.Parsing.Phase1
import Misc

open Batteries (Vector)
open Lean hiding HashMap
open Meta Elab
open Std (HashMap)

namespace Lustrean.Parsing

namespace Phase2
  inductive Expr (n : Nat) where
    | literal (k : &Nat)
    | var (k : &Fin n)
    | mon_op (op : MonOp) (e : &Expr n)
    | bin_op (op : BinOp) (left right : &Expr n)
    deriving Repr, Inhabited

  partial def elab_expr {n : Nat} (env : HashMap Name (Fin n)) (e : &Phase1.Expr) : CoreM (&Expr n) :=
    e.mapM fun
      | .literal k => return .literal k
      | .var ⟨name, ref⟩ => do
        let some k := env.get? name | throwErrorAt ref "unbound variable"
        return .var ⟨k, ref⟩
      | .mon_op op e => do
        let e ← elab_expr env e
        return .mon_op op e
      | .bin_op op left right => do
        let left ← elab_expr env left
        let right ← elab_expr env right
        return .bin_op op left right

  structure Variable (n : Nat) where
    name : &Name
    type : &Name
    value : Option (&Expr n)
    deriving Repr, Inhabited

  structure Node where
    n : Nat
    vars : Vector (Variable n) n
    output_vars : Array (Fin n)
    deriving Repr

  instance : Inhabited Node where
    default := {
      n := 0
      vars := .mk #[] rfl
      output_vars := #[]
    }

  def elab_node (nod : &Phase1.Node) : CoreM (&Node) := nod.mapM fun nod => do
    let vars := Vector.mk nod.vars rfl
    let n := vars.size
    let mut env := {}
    for h : i in [0:vars.size] do
      env := env.insert vars[i].name ⟨i, Membership.get_elem_helper h rfl⟩
    let vars' ← vars.mapM fun var => do
      let { name, type, value } := var
      let some value := value | return { name, type, value := none }
      let value ← elab_expr env value
      return { name, type, value := some value : Variable _ }
    let output_vars ← nod.output_vars.mapM (m := CoreM) fun var => do
      let some i := env.get? var | throwErrorAt var.ref "unbound variable"
      return i
    return { n, vars := vars', output_vars }
end Phase2

end Lustrean.Parsing
