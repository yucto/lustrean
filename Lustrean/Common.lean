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

-- no negated expression. it must be eliminated by simplification
inductive BExpr (n : Nat) : Type :=
| random : BExpr n
| const : Bool → BExpr n
| compare : IExpr n → CompareOp → IExpr n → BExpr n
| and : BExpr n → BExpr n → BExpr n
| or : BExpr n → BExpr n → BExpr n


inductive Instruction (n : Nat) : Type :=
| skip : Instruction n
| assign : Fin n → IExpr n → Instruction n
| guard : BExpr n → Instruction n
