namespace Lustrean

inductive IntOp : Type where
| iadd : IntOp
| isub : IntOp
| imul : IntOp
| idiv : IntOp
deriving Repr, Inhabited

namespace IntOp
protected def toString : IntOp → String
  | .iadd => "+"
  | .isub => "-"
  | .imul => "*"
  | .idiv => "/"

instance : ToString IntOp where
  toString := IntOp.toString
end IntOp

-- n : number of variable
inductive IExpr (n : Nat) : Type where
| nil : IExpr n
| var : Fin n → IExpr n
| rand : Option Int → Option Int → IExpr n
| neg : IExpr n → IExpr n
| binop : IExpr n → IntOp → IExpr n → IExpr n
deriving Repr, Inhabited

namespace IExpr
variable {n : Nat}

def const (x : Int) : IExpr n :=
  .rand x x

protected def toString : IExpr n → String
  | .nil => "nil"
  | .var k => toString k
  | .rand left right =>
    let l := match left with
      | some n => toString n
      | none => "-∞"
    let r := match right with
      | some n => toString n
      | none => "∞"
    s!"[{l}, {r}]"
  | .neg e => s!"(- {e.toString})"
  | .binop left op right => s!"({op} {left.toString} {right.toString})"

instance : ToString (IExpr n) where
  toString := IExpr.toString
end IExpr

inductive CompareOp : Type where
| eq : CompareOp
| neq : CompareOp
| le : CompareOp
| lt : CompareOp
| ge : CompareOp
| gt : CompareOp
deriving Repr, Inhabited

namespace CompareOp
def not : CompareOp → CompareOp
| eq => neq
| neq => eq
| le => gt
| lt => ge
| ge => lt
| gt => le

protected def toString : CompareOp → String
  | eq => "="
  | neq => "≠"
  | le => "≤"
  | lt => "<"
  | ge => "≥"
  | gt => ">"

instance : ToString CompareOp where
  toString := CompareOp.toString
end CompareOp

-- no negated expression. it must be eliminated by simplification
inductive BExpr (n : Nat) : Type where
| random : BExpr n
| const : Bool → BExpr n
| compare : IExpr n → CompareOp → IExpr n → BExpr n
| and : BExpr n → BExpr n → BExpr n
| or : BExpr n → BExpr n → BExpr n
deriving Repr, Inhabited

namespace BExpr
variable {n : Nat}

def not : BExpr n → BExpr n
  | random => random
  | const b => const (.not b)
  | compare a op b => compare a op.not b
  | and b b' => or b.not b'.not
  | or b b' => and b.not b'.not

protected def toString : BExpr n → String
  | .random => "?"
  | .const b => toString b
  | .compare left op right => s!"({op} {left} {right})"
  | .and left right => s!"(and {left.toString} {right.toString})"
  | .or left right => s!"(or {left.toString} {right.toString})"

instance : ToString (BExpr n) where
  toString := BExpr.toString
end BExpr

inductive Instruction (n : Nat) : Type where
| skip : Instruction n
| assign : Fin n → IExpr n → Instruction n
| guard : BExpr n → Instruction n
| assert : BExpr n → Instruction n
deriving Repr, Inhabited

namespace Instruction
variable {n : Nat}

protected def toString : Instruction n → String
  | .skip => "skip"
  | .assign k e => s!"x_{k} := {e}"
  | .guard b => s!"guard {b}"
  | .assert b => s!"assert {b}"

instance : ToString (Instruction n) where
  toString := Instruction.toString
end Instruction

structure OutNode (nb_var : Nat) where
  out_node: Nat
  out_inst : Instruction nb_var
  ref? : Option (Lean.Syntax) := none
deriving Repr

structure PreNode (nb_var : Nat) : Type where
  id : Nat
  out_nodes : List (OutNode nb_var)
  deriving Repr, Inhabited

section
open Std.Format
open Std.ToFormat

instance {n} : Std.ToFormat (OutNode n) where
  format node := paren ("l_" ++ format node.out_node) ++ " " ++ format node.out_inst

instance {n}: Std.ToFormat (PreNode n) where
  format p :=
    "node f_" ++ format p.id ++ " where" ++ (indentD <| joinSep p.out_nodes line)
end
end Lustrean
