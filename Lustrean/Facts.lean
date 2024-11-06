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

  theorem max_min_absorb : ∀ (n m :Int),
    max n (min n m) = n :=
  by
    intro n m
    apply Int.max_eq_left
    apply Int.min_le_left
end Int
