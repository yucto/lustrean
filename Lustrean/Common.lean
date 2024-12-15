inductive int_op : Type :=
| iadd : int_op
| isub : int_op
| imul : int_op
| idiv : int_op

-- n : number of variable
inductive iexpr (n : Nat) : Type :=
| nil : iexpr n
| var : Fin n → iexpr n
| rand : Int → Int → iexpr n
| const : Int → iexpr n
| neg : iexpr n → iexpr n
| binop : iexpr n → int_op → iexpr n → iexpr n

inductive compare_op : Type :=
| ceq : compare_op
| cneq : compare_op
| cle : compare_op
| clt : compare_op
| cge : compare_op
| cgt : compare_op

-- no negated expression. it must be eliminated by simplification
inductive bexpr (n : Nat) : Type :=
| random : bexpr n
| const : Bool → bexpr n
| compare : iexpr n → compare_op → iexpr n → bexpr n
| and : bexpr n → bexpr n → bexpr n
| or : bexpr n → bexpr n → bexpr n


inductive inst (n : Nat) : Type :=
| skip : inst n
| assign : Fin n → iexpr n → inst n
| guard : bexpr n → inst n
