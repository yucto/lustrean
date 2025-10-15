import Batteries.Data.Vector.Basic

namespace Batteries.Vector

/-- Map a monadic function over a vector. -/
def mapM {α β m} [Monad m] (f : α → m β) {n} (v : Vector α n) : m (Vector β n) := do
  go 0 (Nat.zero_le n) (.emptyWithCapacity n)
where
  go (i : Nat) (h : i ≤ n) (r : Vector β i) : m (Vector β n) := do
    if h' : i < n then
      go (i+1) (by omega) (r.push (← f v[i]))
    else
      return r.cast (by omega)

@[simp]
theorem get_mk_vector_fin {α n} : ∀ (x : α) (i : Fin n), (Vector.replicate n x).get i = x := by
  intros x i
  apply Vector.getElem_replicate

@[simp]
theorem get_mk_vector_nat {α n} : ∀ (x : α) (i : Nat) (h : i < n), (Vector.replicate  n x)[i] = x := by
  intros x i h
  rw [Vector.replicate]
  have : i < (Vector.replicate n x).size := by simpa using h
  show (Vector.replicate n x)[i] = x
  simp

@[simp]
theorem get_of_fn_fin {α n} : ∀ (f : Fin n → α) (i : Fin n), (Vector.ofFn f).get i = f i := by
  intros f i
  simp [Vector.ofFn]
  show (Array.ofFn f)[i] = f i
  simp

@[simp]
theorem get_of_fn_nat {α n} : ∀ (f : Fin n → α) (i : Nat) (h : i < n), (Vector.ofFn f)[i] = f ⟨i, h⟩ := by
  intros f i h
  simp [Vector.ofFn]

end Batteries.Vector
