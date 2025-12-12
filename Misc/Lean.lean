import Lean.Log
open Lean

def Lean.logErrorAt? {m : Type → Type} [Monad m] [MonadLog m] [AddMessageContext m] [MonadOptions m]
  (ref? : Option Syntax) (msgData : MessageData) : m Unit := do
    if let some ref := ref? then
      logErrorAt ref msgData
    else
      logError msgData

def Array.toStringNoBrackets (xs : Array String) : String :=
  (Std.Format.joinSep xs.toList ("," ++ Std.Format.line)) |>.pretty

def Fin.mk' {n : Nat} (val : Nat) (isLt : val < n := by get_elem_tactic) : Fin n := Fin.mk val isLt

def Std.Format.joinSepArray.{u} {α : Type u} [ToFormat α] (xs : Array α) (sep : Format) : Format :=
  if _ : xs.size = 0 then
    .nil
  else  if _ : xs.size = 1 then
    format xs[0]
  else
    xs[1:].foldl (· ++ sep ++ format ·) (format xs[0])
