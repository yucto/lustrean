import Lean
import Lustrean.Domain
import Lustrean.Parsing

open Lean Meta Elab

elab_rules : command
  | `(command| lustre $nodes:lustre_node*) => do
    for _n in nodes do
      pure ()

class Domain (α : Type _) extends Add α, Mul α, Sub α where
  from_nat : Nat → α
  initial_value : α
export Domain (from_nat initial_value)

inductive Expr (α : Type _) [Domain α] (n : Nat) where
  | Var (k : Fin n)
  | Literal (a : α)
  | Add (left right : Expr α n)
  | Zero
  | Mul (left right : Expr α n)
  | Sub (left right : Expr α n)

def Env (α : Type _) [Domain α] (n : Nat) : Type :=
  { a : Array (Expr α n) // a.size = n }

structure StateMachine.{u} (α : Type _) [Domain α] (Input : Type u) : Type u where
  n : Nat
  state : Env α n
  transition : Env α n → Input → Env α n

lustre
  node hello(x : nat, y : nat) = o where
    o = x * y + 5

  node au_revoir() where
    o : nat = 3
