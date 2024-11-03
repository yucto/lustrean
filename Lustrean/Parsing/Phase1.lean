import Lustrean.Parsing.Syntax

open Lean Meta Elab

namespace Lustrean.Parsing
structure WithRef (α : Type _) where
  value : α
  ref : Syntax
  deriving Repr, Inhabited

namespace WithRef
  prefix:50 "&" => WithRef
  
  instance (α : Type _) : CoeSort (&α) α where
    coe := value
end WithRef

namespace Phase1
  inductive Expr where
    | literal (k : &Nat)
    | add (left right : &Expr)
    | sub (left right : &Expr)
    | mul (left right : &Expr)
    | var (name : &Name)
    | neg (e : &Expr)
    | pre (e : &Expr)
    | arrow (left right : &Expr)
    deriving Repr, Inhabited

  partial def elab_expr (s : Lean.TSyntax `lustre_expr ) : CoreM (&Expr) := do
    let expr : Expr ← match s with
      | `(lustre_expr| $n:num) => pure <| .literal ⟨n.getNat, n⟩
      | `(lustre_expr| $v:ident) => pure <| .var ⟨v.getId, v⟩
      | `(lustre_expr| $l + $r) =>
        let left ← elab_expr l
        let right ← elab_expr r
        pure <| .add left right
      | `(lustre_expr| pre $e) =>
        let e ← elab_expr e
        pure <| .pre e
      | `(lustre_expr| - $e) =>
        let e ← elab_expr e
        pure <| .neg e
      | `(lustre_expr| $l * $r) =>
        let left ← elab_expr l
        let right ← elab_expr r
        pure <| .mul left right
      | `(lustre_expr| $l - $r) =>
        let left ← elab_expr l
        let right ← elab_expr r
        pure <| .sub left right
      | `(lustre_expr| $l → $r) =>
        let left ← elab_expr l
        let right ← elab_expr r
        pure <| .arrow left right
      | _ => throwUnsupportedSyntax
    return ⟨expr, s⟩

  structure Variable where
    name : &Name
    type : &Name
    value : Option (&Expr)
    deriving Repr, Inhabited

  structure Node where
    name : &Name
    vars : Array Variable
    output_vars : Array (&Name)
    deriving Repr, Inhabited

  def elab_node (s : TSyntax `lustre_node) : CoreM (&Node) := match s with
    | `(lustre_node| node $name($inputs:lustre_binding,*) $[= $output_vars,*]? where
                     $decls*) => do
      let name := ⟨name.getId, name⟩
      let input_vars ← inputs.getElems.mapM fun
        | `(lustre_binding| $name:ident : $type:ident) => pure {
          name := ⟨name.getId, name⟩
          type := ⟨type.getId, type⟩
          value := none
        }
        | _ => throwUnsupportedSyntax
      let local_vars ← decls.mapM fun
        | `(lustre_node_decl| $var:ident : $type:ident = $expr:lustre_expr) => do pure {
          name := ⟨var.getId, var⟩
          type := ⟨type.getId, type⟩
          value := ← elab_expr expr
        }
        | _ => throwUnsupportedSyntax
      let vars := input_vars ++ local_vars
      let output_vars := output_vars.map (·.getElems.map (fun var => ⟨var.getId, var⟩)) |>.getD default
      return ⟨{name, vars, output_vars}, s⟩
    | _ => throwUnsupportedSyntax
end Phase1
end Lustrean.Parsing
