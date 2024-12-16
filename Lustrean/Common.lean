inductive IntOp : Type :=
| iadd : IntOp
| isub : IntOp
| imul : IntOp
| idiv : IntOp

-- n : number of variable
inductive IExpr (n : Nat) : Type :=
| nil : IExpr n
| var : Fin n → IExpr n
| rand : Int → Int → IExpr n
| const : Int → IExpr n
| neg : IExpr n → IExpr n
| binop : IExpr n → IntOp → IExpr n → IExpr n

inductive CompareOp : Type :=
| ceq : CompareOp
| cneq : CompareOp
| cle : CompareOp
| clt : CompareOp
| cge : CompareOp
| cgt : CompareOp

def CompareOp.not (c : CompareOp) := match c with
| ceq => cneq
| cneq => ceq
| cle => cgt
| clt => cge
| cge => clt
| cgt => cle

-- no negated expression. it must be eliminated by simplification
inductive BExpr (n : Nat) : Type :=
| random : BExpr n
| const : Bool → BExpr n
| compare : IExpr n → CompareOp → IExpr n → BExpr n
| and : BExpr n → BExpr n → BExpr n
| or : BExpr n → BExpr n → BExpr n

def BExpr.not {n : Nat} (b : BExpr n) := match b with
| random => random
| const b => const (.not b)
| compare a op b => compare a op.not b
| and b b' => or b.not b'.not
| or b b' => and b.not b'.not

inductive Instruction (n : Nat) : Type :=
| skip : Instruction n
| assign : Fin n → IExpr n → Instruction n
| guard : BExpr n → Instruction n
| assert : BExpr n → Instruction n

structure PreNode (nb_var : Nat) : Type where
  id : Nat
  out_nodes : List (Nat × Instruction nb_var × Lean.Syntax)
