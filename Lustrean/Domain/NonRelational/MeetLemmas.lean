import Batteries.Data.Vector.Basic
import Lustrean.Domain.NonRelational.Basic

open Batteries

namespace Lustrean.NonRelational
  variable {α : Type} {n : Nat}
  variable [ι : ValueDomain α]
  variable (x y z : NonRelational α n)

  theorem meet_commutative : meet x y = meet y x := by
    cases x <;> cases y <;> simp [meet, map2Nil, coalesce]
    rename_i x y
    simp [BoundedLattice.meet_commutative]
    split <;> rename_i h
    · rw [dif_pos]
      intros i
      simp
      rw [BoundedLattice.meet_commutative]
      simpa using h i
    · rw [dif_neg]
      intro h'
      apply h
      intro i
      have h' := h' i
      simp at h' ⊢
      rw [BoundedLattice.meet_commutative]
      assumption

theorem meet_associative : meet (meet x y) z = meet x (meet y z) := by
    cases x <;> cases y <;> simp [meet, map2Nil, coalesce] ; cases z
    case bot => simp
    rename_i x y z
    by_cases H : ∀ i : Fin n, x.val.get i ⊓ y.val.get i ⊓ z.val.get i ≠ ⊥
    · rw [dif_pos]
      dsimp
      rw [dif_pos, dif_pos]
      simp
      assumption

      all_goals
        intros i ; specialize H i;
        have H' : (x.val.get i ⊓ y.val.get i) ⊓ z.val.get i ≠ ⊥ := by {
        rw [BoundedLattice.meet_associative]
        apply H
        }
      · simp
        apply BoundedLattice.meet_not_bot_left (y := x.val.get i)
        rw [BoundedLattice.meet_commutative]
        assumption
      · simp [*]
      · simp
        apply BoundedLattice.meet_not_bot_left (y := z.val.get i)
        assumption
    · have : ¬∀ i : Fin n,
           (Vector.ofFn fun i =>
             (Vector.ofFn fun i => x.val.get i ⊓ y.val.get i).get i ⊓ z.val.get i
           ).get i ≠ ⊥ := by
        let β (i : Fin n) :=
          (Vector.ofFn fun i => (Vector.ofFn fun i => x.val.get i ⊓ y.val.get i).get i ⊓ z.val.get i).get i ≠ ⊥
        let β' (i : Fin n) :=
          (x.val.get i ⊓ y.val.get i) ⊓ z.val.get i ≠ ⊥
        have (i : Fin n) : β i = β' i := by simp [β, β']
        rw [piext β β' this]
        intros Hc
        apply H
        intros i
        rw [← BoundedLattice.meet_associative]
        apply Hc
      have l : (∀ (i : Fin n), (Vector.ofFn fun i => x.val.get i ⊓ y.val.get i).get i ≠ ⊥)
               = (∀ (i : Fin n), x.val.get i ⊓ y.val.get i ≠ ⊥) := by
        piext i
        simp
      by_cases H' : ∀ (i : Fin n), x.val.get i ⊓ y.val.get i ≠ ⊥ <;> simp
      · rw [← l] at H'
        rw [dif_pos H']
        dsimp only []
        rw [dif_neg this]
        by_cases y_z_bot : ∀ i, (Vector.ofFn fun i => y.val.get i ⊓ z.val.get i).get i ≠ ⊥
        · rw [dif_pos y_z_bot]
          dsimp only []
          rw [dif_neg]
          intro a
          apply H
          intro i
          specialize a i
          rw [Vector.get_of_fn_fin, Vector.get_of_fn_fin] at a
          assumption
        · rw [dif_neg y_z_bot]
      · rw [← l] at H'
        rw [dif_neg H']
        dsimp only []
        by_cases y_z_bot : ∀ i, (Vector.ofFn fun i => y.val.get i ⊓ z.val.get i).get i ≠ ⊥
        · rw [dif_pos y_z_bot]
          dsimp only []
          rw [dif_neg]
          intro a
          apply H
          intro i
          specialize a i
          rw [Vector.get_of_fn_fin, Vector.get_of_fn_fin] at a
          assumption
        · rw [dif_neg y_z_bot]

  theorem meet_absorption : meet x (join x y) = x := by
    cases x <;> cases y <;> simp [meet, join, map2Nil, coalesce]
    case bot x =>
      simp [BoundedLattice.meet_idempotent, x.property]
      ext
      simp
      rfl
    rename_i x y
    rw [dif_pos]
    · congr
      ext
      simp
      rfl
    simp [BoundedLattice.meet_absorption, x.property]

  theorem meet_top : x.meet top = x := by
    cases x <;> simp [meet, top, map2Nil, coalesce]
    rename_i x
    rw [dif_pos]
    · congr
      ext
      simp
      rfl
    · simp [BoundedLattice.meet_top, x.property]

  theorem meet_bot : x.meet bot = bot := by
    cases x <;> simp [meet, map2Nil]
end Lustrean.NonRelational
