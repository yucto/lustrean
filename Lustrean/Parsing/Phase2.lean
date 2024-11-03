import Lustrean.Parsing.Phase1

open Lean hiding HashMap
open Meta Elab
open Std (HashMap)

namespace Lustrean.Parsing

namespace Phase2
  inductive Expr (n : Nat) where
    | literal (k : &Nat)
    | add (left right : &Expr n)
    | sub (left right : &Expr n)
    | mul (left right : &Expr n)
    | var (k : &Fin n)
    | neg (e : &Expr n)
    | pre (e : &Expr n)
    | arrow (left right : &Expr n)
    deriving Repr, Inhabited

  def elab_expr {n : Nat} (env : HashMap Name (Fin n)) (e : &Phase1.Expr) : Except Syntax (&Expr n) := do
    let ⟨e, ref⟩ := e
    let result ← match e with
      | .literal k => pure <| .literal k
      | .add left right =>
        let left ← elab_expr env left
        let right ← elab_expr env right
        pure <| .add left right
      | .sub left right =>
        let left ← elab_expr env left
        let right ← elab_expr env right
        pure <| .sub left right
      | .mul left right =>
        let left ← elab_expr env left
        let right ← elab_expr env right
        pure <| .mul left right
      | .var ⟨name, ref⟩ =>
        let some k := env.get? name | .error ref
        pure <| .var ⟨k, ref⟩
      | .neg e =>
        let e ← elab_expr env e
        pure <| .neg e
      | .pre e =>
        let e ← elab_expr env e
        pure <| .pre e
      | .arrow left right =>
        let left ← elab_expr env left
        let right ← elab_expr env right
        pure <| .arrow left right
    return ⟨result, ref⟩

  structure Variable (n : Nat) where
    name : &Name
    type : &Name
    value : Option (&Expr n)
    deriving Repr, Inhabited

  structure Node where
    n : Nat
    vars : Array (Variable n)
    output_vars : Array (Fin n)
    vars_size : vars.size = n
    deriving Repr

  instance : Inhabited Node where
    default := {
      n := 0
      vars := #[]
      output_vars := #[]
      vars_size := rfl
    }

  -- Poor man's `mapM`.  The reason to have this is that proving that `Array.mapM` preserves the
  -- size, assuming that it returns something of the form `pure _` and that the monad has nice
  -- properties, is actually harder than recoding it by hand.
  def pmmapM {ε n} (f : Phase1.Variable → Except ε (Variable n))
               : List Phase1.Variable → Except ε (List (Variable n))
    | [] => pure []
    | hd::tl => do
      let hd' ← f hd
      let tl' ← pmmapM f tl
      return hd'::tl'

  theorem pmmapM_size {ε n} (f : Phase1.Variable → Except ε (Variable n))
                        (as : List Phase1.Variable) (bs : List (Variable n))
                        : pmmapM f as = .ok bs → bs.length = as.length := by
    induction as generalizing bs with
    | nil =>
      intro h
      simp [pmmapM] at h ⊢
      cases h
      rfl
    | cons hd tl ih =>
      simp [pmmapM]
      cases f hd
      case error =>
        intro h
        cases h
      revert ih
      cases pmmapM f tl <;> intro ih
      case error =>
        intro h
        cases h
      intro h
      cases h
      rename_i hd' tl'
      simp
      apply ih
      rfl

  def elab_node (nod : &Phase1.Node) : CoreM (&Node) := do
    let ⟨nod, ref⟩ := nod
    let n := nod.vars.size
    let mut env := {}
    for h : i in [0:n] do
      env := env.insert nod.vars[i].name ⟨i, Membership.get_elem_helper h rfl⟩
    let maybe_vars := pmmapM (fun var => do
      let { name, type, value } := var
      let some value := value | return { name, type, value := none }
      return { name, type, value := some <| ← elab_expr env value : Variable n }) nod.vars.data
    match h : maybe_vars with
      | .ok vars =>
        let output_vars ← nod.output_vars.mapM (m := CoreM) fun var : (&Name) => do
          let some i := env.get? var | throwErrorAt var.ref "variable not found"
          return i
        let vars_size := by
          simp
          apply pmmapM_size
          assumption
        return ⟨{ n, vars := .mk vars, output_vars, vars_size }, ref⟩
      | .error ref => throwErrorAt ref "variable not found"
end Phase2

end Lustrean.Parsing
