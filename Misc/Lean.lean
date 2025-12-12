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
