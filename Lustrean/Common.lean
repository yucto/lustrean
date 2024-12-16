namespace Lustrean

inductive IntOp : Type where
| iadd : IntOp
| isub : IntOp
| imul : IntOp
| idiv : IntOp
deriving Repr, Inhabited

-- n : number of variable
inductive IExpr (n : Nat) : Type where
| nil : IExpr n
| var : Fin n → IExpr n
| rand : Option Int → Option Int → IExpr n
| neg : IExpr n → IExpr n
| binop : IExpr n → IntOp → IExpr n → IExpr n
deriving Repr, Inhabited

inductive CompareOp : Type where
| ceq : CompareOp
| cneq : CompareOp
| cle : CompareOp
| clt : CompareOp
| cge : CompareOp
| cgt : CompareOp
deriving Repr, Inhabited

def CompareOp.not : CompareOp → CompareOp
| ceq => cneq
| cneq => ceq
| cle => cgt
| clt => cge
| cge => clt
| cgt => cle

-- no negated expression. it must be eliminated by simplification
inductive BExpr (n : Nat) : Type where
| random : BExpr n
| const : Bool → BExpr n
| compare : IExpr n → CompareOp → IExpr n → BExpr n
| and : BExpr n → BExpr n → BExpr n
| or : BExpr n → BExpr n → BExpr n
deriving Repr, Inhabited

def BExpr.not {n : Nat} : BExpr n → BExpr n
| random => random
| const b => const (.not b)
| compare a op b => compare a op.not b
| and b b' => or b.not b'.not
| or b b' => and b.not b'.not

inductive Instruction (n : Nat) : Type where
| skip : Instruction n
| assign : Fin n → IExpr n → Instruction n
| guard : BExpr n → Instruction n
| assert : BExpr n → Instruction n
deriving Repr, Inhabited

structure PreNode (nb_var : Nat) : Type where
  id : Nat
  out_nodes : List (Nat × Instruction nb_var × Lean.Syntax)
  deriving Repr, Inhabited

end Lustrean
