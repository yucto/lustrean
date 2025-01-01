import Lustrean.Elaboration.Syntax

open Lean Meta Elab

-- Reify phase.  This is the bridge between the parser and the elaborator.

namespace Lustrean.Elaboration
structure WithRef (α : Type _) where
  value : α
  ref : Syntax
  deriving Repr, Inhabited

namespace WithRef
  prefix:50 "&" => WithRef

  instance (α : Type _) : CoeSort (&α) α where
    coe := value

  protected def toString {α} [ToString α] (self : &α) :=
    toString self.value

  instance {α} [ToString α] : ToString (&α) where
    toString := WithRef.toString

  protected abbrev map {α β} (self : &α) (f : α → β) : &β where
    ref := self.ref
    value := f self.value

  protected abbrev mapM {α β m} [Monad m] (self : &α) (f : α → m β) : m (&β) := do
    let ⟨value, ref⟩ := self
    let value' ← f value
    return ⟨value', ref⟩

  def withRefM {α m} [Monad m] (ref : Syntax) (value : m α) : m (&α) := do
    return {
      value := ← value
      ref
    }
end WithRef

inductive LowerBound where
  | nat (n : Nat)
  | minf
  deriving Repr, Inhabited

namespace LowerBound
  protected def toString : LowerBound → String
    | .nat n => toString n
    | .minf => "-∞"

  instance : ToString LowerBound where
    toString := LowerBound.toString

  instance (n : Nat) : OfNat LowerBound n where
    ofNat := .nat n
end LowerBound

inductive UpperBound where
  | nat (n : Nat)
  | pinf
  deriving Repr, Inhabited

namespace UpperBound
  protected def toString : UpperBound → String
    | .nat n => toString n
    | .pinf => "∞"

  instance : ToString UpperBound where
    toString := UpperBound.toString

  instance (n : Nat) : OfNat UpperBound n where
    ofNat := .nat n
end UpperBound

inductive MonOp where
  | neg
  deriving Repr, Inhabited

namespace MonOp
  protected def toString : MonOp → String
    | neg => "-"

  instance : ToString MonOp where
    toString := MonOp.toString
end MonOp

inductive CmpOp where
  | eq
  | leq
  | lt
  deriving Repr, Inhabited

namespace CmpOp
  protected def toString : CmpOp → String
    | eq => "="
    | leq => "≤"
    | lt => "<"

  instance : ToString CmpOp where
    toString := CmpOp.toString
end CmpOp

inductive BoolBinOp where
  | and
  | or
  deriving Repr, Inhabited

namespace BoolBinOp
  protected def toString : BoolBinOp → String
    | and => "∧"
    | or => "∨"

  instance : ToString BoolBinOp where
    toString := BoolBinOp.toString
    
end BoolBinOp

namespace Reify
  inductive BinOp where
    | add
    | sub
    | mul
    | fby
    deriving Repr, Inhabited

  namespace BinOp
    protected def toString : BinOp → String
      | .add => "+"
      | .sub => "-"
      | .mul => "*"
      | .fby => "fby"

    instance : ToString BinOp where
      toString := BinOp.toString
  end BinOp

  mutual
    inductive Expr where
      | int (lb : &LowerBound) (up : &UpperBound)
      | var (name : &Name)
      | mon_op (op : MonOp) (e : &Expr)
      | bin_op (op : BinOp) (left right : &Expr)
      | node (name : &Name) (args : Array (&Expr))
      | ite (cond : &BoolExpr) (tb : &Expr) (eb : &Expr)
      deriving Repr, Inhabited

    inductive BoolExpr where
      | cmp_op (op : CmpOp) (left right : &Expr)
      | bin_op (op : BoolBinOp) (left right : &BoolExpr)
      deriving Repr, Inhabited
  end

  structure Variable where
    name : &Name
    deriving Repr, Inhabited

  structure BoundVars where
    names : Array (&Name)
    value : &Expr
    deriving Repr, Inhabited

  structure Node where
    name : &Name
    input_vars : Array Variable
    bound_vars : Array BoundVars
    output_vars : Array (&Name)
    guards : Array (&BoolExpr)
    asserts : Array (&BoolExpr)
    deriving Repr, Inhabited

  mutual
    partial def elab_expr (s : TSyntax `lustre_expr ) : CoreM (&Expr) :=
      WithRef.withRefM s do match s with
        | `(lustre_expr| [$lbs, $ups]) =>
          let lb ← match lbs with
            | `(lustre_lower_bound| -∞) => pure .minf
            | `(lustre_lower_bound| $n:num) => pure <| .nat n.getNat
            | _ => throwUnsupportedSyntax
          let up ← match ups with
            | `(lustre_upper_bound| ∞) => pure .pinf
            | `(lustre_upper_bound| $n:num) => pure <| .nat n.getNat
            | _ => throwUnsupportedSyntax
          return .int ⟨lb, lbs⟩ ⟨up, ups⟩
        | `(lustre_expr| $v:ident) => return .var ⟨v.getId, v⟩
        | `(lustre_expr| $l + $r) =>
          let left ← elab_expr l
          let right ← elab_expr r
          return .bin_op .add left right
        | `(lustre_expr| $l fby $r) =>
          let left ← elab_expr l
          let right ← elab_expr r
          return .bin_op .fby left right
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
        | `(lustre_expr| $f:ident($args:lustre_expr,*)) =>
          let args ← args.getElems.mapM elab_expr
          return .node ⟨f.getId, f⟩ args
        | `(lustre_expr| if $c then $tb else $eb) =>
          let c ← elab_bool_expr c
          let tb ← elab_expr tb
          let eb ← elab_expr eb
          return .ite c tb eb
        | _ =>
          -- withRef s throwUnsupportedSyntax
          throwErrorAt s m!"{repr s}"

      partial def elab_bool_expr (s : TSyntax `lustre_assertion) : CoreM (&BoolExpr) :=
        WithRef.withRefM s do match s with
          | `(lustre_assertion| $l:lustre_expr ≤ $r:lustre_expr) =>
            let left ← elab_expr l
            let right ← elab_expr r
            return .cmp_op .leq left right
          | `(lustre_assertion| $l:lustre_expr = $r:lustre_expr) =>
            let left ← elab_expr l
            let right ← elab_expr r
            return .cmp_op .eq left right
          | `(lustre_assertion| $l:lustre_expr < $r:lustre_expr) =>
            let left ← elab_expr l
            let right ← elab_expr r
            return .cmp_op .lt left right
          | `(lustre_assertion| $l:lustre_assertion ∧ $r:lustre_assertion) =>
            let left ← elab_bool_expr l
            let right ← elab_bool_expr r
            return .bin_op .and left right
          | `(lustre_assertion| $l:lustre_assertion ∨ $r:lustre_assertion) =>
            let left ← elab_bool_expr l
            let right ← elab_bool_expr r
            return .bin_op .or left right
          | ref =>
            println! s!"{repr ref}"
            withRef ref throwUnsupportedSyntax
  end

  def elab_node (s : TSyntax `lustre_node) : CoreM (&Node) := do match s with
    | `(lustre_node| node $name($inputs:ident,*) $[= $output_vars,*]? $[guard $guards*]?
                     where $decls* $[assert $asserts*]?) =>
      let name := ⟨name.getId, name⟩
      let input_vars := inputs.getElems.map fun x => ⟨x.getId, x⟩
      let bound_vars ← decls.mapM fun
        | `(lustre_node_decl| $vars:ident,* = $expr:lustre_expr) => do pure {
          names := vars.getElems.map fun var => ⟨var.getId, var⟩
          value := ← elab_expr expr
        }
        | ref => withRef ref throwUnsupportedSyntax
      let output_vars := output_vars.map (·.getElems.map (fun var => ⟨var.getId, var⟩)) |>.getD default
      let guards ← guards.getD #[] |>.mapM elab_bool_expr
      let asserts ← asserts.getD #[] |>.mapM elab_bool_expr
      return ⟨{name, input_vars, bound_vars, output_vars, guards, asserts}, s⟩
    | _ =>
      throwUnsupportedSyntax

  def elab_lustre (nodes : TSyntaxArray `lustre_node) : CoreM (Array (&Node)) :=
    nodes.mapM elab_node
end Reify
end Lustrean.Elaboration
