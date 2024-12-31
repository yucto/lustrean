namespace Int
  variable (n m o : Int)

  theorem min_assoc : min (min n m) o = min n (min m o) := by
    repeat rw [Int.min_def]
    repeat' split
    all_goals omega

  theorem max_assoc : max (max n m) o = max n (max m o) := by
    repeat rw [Int.max_def]
    repeat' split
    all_goals omega

  theorem min_max_absorb : min n (max n m) = n := by
    apply Int.min_eq_left
    apply Int.le_max_left

  theorem max_min_absorb : max n (min n m) = n := by
    apply Int.max_eq_left
    apply Int.min_le_left
end Int
