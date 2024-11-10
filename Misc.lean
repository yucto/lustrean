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

end Batteries.Vector
