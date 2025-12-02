import Lustrean.Domain.NonRelational.Lattice
import Lustrean.Domain.NonRelational.Widen

open Batteries

namespace Lustrean.NonRelational
  variable {α : Type} {n : Nat}
  variable [ι : ValueDomain α]

  protected def narrow (x y : NonRelational α n) (m : Nat) := map2Nil x y fun x y => Vector.ofFn fun i =>
    Narrow.narrow (x.get i) (y.get i) m

  instance : Narrow (NonRelational α n) where
    narrow := NonRelational.narrow

  instance : NarrowLawful (NonRelational α n) where
    bounding_low := by
      intros x y m
      cases x <;> cases y <;> simp [Narrow.narrow, NonRelational.narrow, meet, map2Nil, coalesce]
      ;(try apply BoundedLattice.bot_min)
      ;(try apply BoundedLattice.refl)
      rename_i x y
      split
      case isFalse => apply BoundedLattice.bot_min
      case isTrue H =>
        -- have H' : ∀ i : Fin n, Narrow.narrow (x.val.get i) (y.val.get i) n ≠ ⊥ := by
        rw [dif_pos]
        case hc =>
          intros i Hc
          apply H i
          apply BoundedLattice.min_bot_is_bot
          conv =>
            rhs
            rw [← Hc]
          simp
          apply NarrowLawful.bounding_low
        rw [non_rel_subset]
        intros i
        simp
        apply NarrowLawful.bounding_low
      all_goals rfl

    bounding_high := by
      intros x y n
      cases x <;> cases y <;> simp [Narrow.narrow, NonRelational.narrow, map2Nil, coalesce]
      ; (try apply BoundedLattice.bot_min)
      ; (try apply BoundedLattice.refl)
      rename_i x y
      split
      case isFalse => apply BoundedLattice.bot_min
      case isTrue H =>
        rw [non_rel_subset]
        intros i
        simp
        apply NarrowLawful.bounding_high
      all_goals rfl
end Lustrean.NonRelational
