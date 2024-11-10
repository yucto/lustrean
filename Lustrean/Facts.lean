namespace Int
  theorem min_assoc : ∀ (n m o : Int),
    min (min n m) o = min n (min m o) :=
  by
    intro n m o
    repeat rw [Int.min_def]
    repeat' split
    all_goals omega

  theorem max_assoc : ∀ (n m o : Int),
    max (max n m) o = max n (max m o) :=
  by
    intro n m o
    repeat rw [Int.max_def]
    repeat' split
    all_goals omega

  theorem min_max_absorb : ∀ (n m : Int),
    min n (max n m) = n :=
  by
    intro n m
    apply Int.min_eq_left
    apply Int.le_max_left

  theorem max_min_absorb : ∀ (n m : Int),
    max n (min n m) = n :=
  by
    intro n m
    apply Int.max_eq_left
    apply Int.min_le_left

  theorem min_alternative : ∀ (n m : Int),
    min n m = n ∨ min n m = m :=
  by
    intros n m
    rw [Int.min_def]
    split
    · left <;> rfl
    · right <;> rfl

  theorem max_alternative : ∀ (n m : Int),
    max n m = n ∨ max n m = m :=
  by
    intros n m
    rw [Int.max_def]
    split
    · right <;> rfl
    · left <;> rfl
end Int

namespace Decidable
  def decide_and : ∀ (p q : Prop),
    Decidable p -> Decidable q -> Decidable (p ∧ q) :=
  by
    intros p q ι ι'
    cases ι <;> cases ι' <;>
    rename_i h h' <;>
    (try apply Decidable.isTrue <;> constructor <;> assumption) <;>
    apply Decidable.isFalse <;>
    intros H <;>
    cases H <;>
    solve | apply h <;> assumption | apply h' <;> assumption
end Decidable
