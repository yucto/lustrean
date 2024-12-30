import Batteries.Data.Vector.Basic

namespace Batteries.Vector

/-- Map a monadic function over a vector. -/
def mapM {α β m} [Monad m] (f : α → m β) {n} (v : Vector α n) : m (Vector β n) := do
  go 0 (Nat.zero_le n) .empty
where
  go (i : Nat) (h : i ≤ n) (r : Vector β i) : m (Vector β n) := do
    if h' : i < n then
      go (i+1) (by omega) (r.push (← f v[i]))
    else
      return r.cast (by omega)

@[simp]
theorem get_mk_vector_fin {α n} : ∀ (x : α) (i : Fin n), (mkVector n x).get i = x := by
  intros x i
  show (mkArray n x)[i] = x
  simp [mkArray]

@[simp]
theorem get_mk_vector_nat {α n} : ∀ (x : α) (i : Nat) (h : i < n), (mkVector n x)[i] = x := by
  intros x i h
  simp [mkVector]
  have : i < (mkArray n x).size := by simpa using h
  show (mkArray n x)[i] = x
  simp [mkArray]

@[simp]
theorem get_of_fn_fin {α n} : ∀ (f : Fin n → α) (i : Fin n), (ofFn f).get i = f i := by
  intros f i
  simp [ofFn]
  show (Array.ofFn f)[i] = f i
  simp

@[simp]
theorem get_of_fn_nat {α n} : ∀ (f : Fin n → α) (i : Nat) (h : i < n), (ofFn f)[i] = f ⟨i, h⟩ := by
  intros f i h
  simp [ofFn]
  have : i < (Array.ofFn f).size := by simpa using h
  show (Array.ofFn f)[i] = f ⟨i, h⟩
  simp
end Batteries.Vector

theorem piext {α} : ∀ β β' : α → Sort _, (∀ x, β x = β' x) → (∀ x, β x) = (∀ x, β' x) := by
  intros β β' βx_eq_β'x
  have : β = β' := by
    funext
    apply βx_eq_β'x
  rw [this]

macro "piext " x:ident : tactic => `(tactic| (apply piext; intro $x:ident))

namespace Lustrean
  def CounterT := StateT Nat

  namespace CounterT
    universe u
    variable {m : Type -> Type u} [Monad m]
    variable {α}

    instance : Monad (CounterT m) :=
      inferInstanceAs (Monad (StateT Nat m))
    instance [LawfulMonad m] : LawfulMonad (CounterT m) :=
      inferInstanceAs (LawfulMonad (StateT Nat m))
    instance (ε) [MonadExceptOf ε m] : MonadExceptOf ε (CounterT m) :=
      inferInstanceAs (MonadExceptOf ε (StateT Nat m))

    def incr : CounterT m Nat := fun c => pure (c, c+1)
    protected def run (a : CounterT m α) : m α := do
      let (x, _) ← a 0
      return x

    protected def monadLift (x : m α) : CounterT m α :=
      fun c => do return (← x, c)

    instance : MonadLift m (CounterT m) where
      monadLift := CounterT.monadLift
  end CounterT

  abbrev CounterM := CounterT Id
end Lustrean
