import Lean

open Lean Meta Elab

declare_syntax_cat lustre_node
declare_syntax_cat lustre_type
declare_syntax_cat lustre_expr
declare_syntax_cat lustre_node_decl

syntax (name := lustre_command) "lustre " lustre_node* : command
syntax "node " ident "(" (ident " : " lustre_type),* ")" (" = " (ident),+)?
  " where" (lustre_node_decl)* : lustre_node

syntax ident (" : " lustre_type)? " = " lustre_expr : lustre_node_decl
syntax ident : lustre_type
syntax num : lustre_expr
syntax:10 lustre_expr:10 " + " lustre_expr:11 : lustre_expr
syntax:20 lustre_expr:20 " * " lustre_expr:21 : lustre_expr
syntax:50 " pre " lustre_expr:50 : lustre_expr
syntax ident : lustre_expr

elab_rules : command
  | `(command| lustre $nodes:lustre_node*) => do
    for node_ in nodes do
      pure ()

example (s : Lean.TSyntax `num) := s.getNat

inductive ExprStx (n : Nat) where
  | num (k : Fin n)

def elab_lustre_expr (n : Nat) (env : Std.HashMap `ident )(s : Lean.TSyntax `lustre_expr) : MetaM ExprStx := do
  match s with
  | `(lustre_expr| $n:num) => return .num n.getNat
  | `(lustre_expr| $l + $r) =>
    let left ← elab_lustre_expr l
  | _ => throwUnsupportedSyntax

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

def hello := "world"
