import Lustrean.Domain

inductive Integers where
| bot : Integers
| top : Integers
| int : Int → Integers

instance : BoundedLattice Integers where
  bot := .bot
  top := .top
  join x y := match x, y with
  | n, .bot | .bot, n => n
  | .int n, .int m => if n = m then .int n else .top
  | _, _ => .top
  meet x y := match x, y with
  | .top, n | n, .top => n
  | .int n, .int m => if n = m then .int n else .bot
  | _, _ => .bot
  join_commutative := by
    intro x y
    cases x <;> cases y <;> dsimp
    split <;> split
    · next h₁ => rw [h₁]
    · next h₁ h₂ => cases h₂ h₁.symm
    · next h₁ h₂ => cases h₁ h₂.symm
    · constructor
  join_associative := by
    intro x y z
    cases x <;> cases y <;> cases z <;> dsimp
    <;> try (next x y =>
      by_cases h : (x = y) <;> simp [h])
    next x y z =>
      by_cases h1 : (x = y) <;>
      by_cases h2 : (y = z) <;>
      simp [h1] <;>
      simp [h2]
      rw [←h2]
      simp [h1]
  join_absorption := by
    intro x y
    cases x <;> cases y <;> simp <;>
    next x y =>
      by_cases h : (x = y) <;>
      simp [h]
  join_top := by
    intro x
    cases x <;> dsimp
  join_bot := by
    intro x
    cases x <;> dsimp
  meet_commutative := by
    intro x y
    cases x <;> cases y <;> dsimp
    split <;> split
    · next h₁ => rw [h₁]
    · next h₁ h₂ => cases h₂ h₁.symm
    · next h₁ h₂ => cases h₁ h₂.symm
    · constructor
  meet_associative := by
    intro x y z
    cases x <;> cases y <;> cases z <;> dsimp
    <;> try (next x y =>
      by_cases h : (x = y) <;> simp [h])
    next x y z =>
      by_cases h1 : (x = y) <;>
      by_cases h2 : (y = z) <;>
      simp [h1] <;>
      simp [h2]
      rw [←h2]
      simp [h1]
  meet_absorption := by
    intro x y
    cases x <;> cases y <;> simp <;>
    next x y =>
      by_cases h : (x = y) <;>
      simp [h]
  meet_top := by
    intro x
    cases x <;> dsimp
  meet_bot := by
    intro x
    cases x <;> dsimp
