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

  def mapM {α β m} [Monad m] (self : WithRef α) (f : α → m β) : m (WithRef β) := do
    let ⟨value, ref⟩ := self
    let value' ← f value
    return ⟨value', ref⟩

  def withRefM {α m} [Monad m] (ref : Syntax) (value : m α) : m (WithRef α) := do
    return {
      value := ← value
      ref
    }
end WithRef

inductive BinOp where
  | add
  | sub
  | mul
  | pre
  | arrow
  deriving Repr, Inhabited

inductive MonOp where
  | pre
  | neg
  deriving Repr, Inhabited

namespace Phase1
  inductive Expr where
    | literal (k : &Nat)
    | var (name : &Name)
    | mon_op (op : MonOp) (e : &Expr)
    | bin_op (op : BinOp) (left right : &Expr)
    deriving Repr, Inhabited

  partial def elab_expr (s : Lean.TSyntax `lustre_expr ) : CoreM (&Expr) :=
    WithRef.withRefM s do match s with
      | `(lustre_expr| $n:num) => return .literal ⟨n.getNat, n⟩
      | `(lustre_expr| $v:ident) => return .var ⟨v.getId, v⟩
      | `(lustre_expr| $l + $r) =>
        let left ← elab_expr l
        let right ← elab_expr r
        return .bin_op .add left right
      | `(lustre_expr| pre $e) =>
        let e ← elab_expr e
        return .mon_op .pre e
      | `(lustre_expr| - $e) =>
        let e ← elab_expr e
        return .mon_op .neg e
      | `(lustre_expr| $l * $r) =>
        let left ← elab_expr l
        let right ← elab_expr r
        return .bin_op .mul left right
      | `(lustre_expr| $l - $r) =>
        let left ← elab_expr l
        let right ← elab_expr r
        return .bin_op .sub left right
      | `(lustre_expr| $l → $r) =>
        let left ← elab_expr l
        let right ← elab_expr r
        return .bin_op .arrow left right
      | _ =>
        println! "hello"
        throwUnsupportedSyntax

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
        | ref => withRef ref throwUnsupportedSyntax
      let local_vars ← decls.mapM fun
        | `(lustre_node_decl| $var:ident : $type:ident = $expr:lustre_expr) => do pure {
          name := ⟨var.getId, var⟩
          type := ⟨type.getId, type⟩
          value := ← elab_expr expr
        }
        | `(lustre_node_decl| $var:ident = $expr:lustre_expr) => do
          throwErrorAt var "no type inference for now"
        | ref => withRef ref throwUnsupportedSyntax
      let vars := input_vars ++ local_vars
      let output_vars := output_vars.map (·.getElems.map (fun var => ⟨var.getId, var⟩)) |>.getD default
      return ⟨{name, vars, output_vars}, s⟩
    | _ => throwUnsupportedSyntax
end Phase1
end Lustrean.Parsing
