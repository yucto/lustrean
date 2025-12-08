import Lustrean.Domain.NonRelational.Basic

namespace Lustrean.NonRelational
variable {α : Type} {n : Nat}
variable [ι : ValueDomain α]
variable (x y z : NonRelational α n)

theorem join_commutative : join x y = join y x := by
  cases x <;> cases y <;> simp [join]
  rename_i x y
  simp [BoundedLattice.join_commutative]

theorem join_associative : join (join x y) z = join x (join y z) := by
  cases x <;> cases y <;> cases z <;> dsimp [join]
  rename_i x y z
  simp

theorem join_absorption : join x (meet x y) = x := by
  cases x <;> cases y <;> simp only [
    meet,
    map2Nil,
    coalesce
  ]
  split <;> simp [join]
  · ext
    simp
    rfl
  · rfl
  all_goals simp [join]

theorem join_bot : x.join bot = x := by
  cases x <;> simp [join]

theorem join_top : x.join top = top := by
  cases x <;> simp [join, top]
  ext
  simp
end Lustrean.NonRelational
