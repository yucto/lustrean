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
  join_bot := by
    intro x
    cases x <;> dsimp
  join_top := by
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
  meet_bot := by
    intro x
    cases x <;> dsimp
  meet_top := by
    intro x
    cases x <;> dsimp

def map_int (x y : Integers) (f : Int → Int →  Integers) : Integers :=
  match x, y with
  | .bot, _ | _, .bot => .bot
  | .top, _ | _, .top => .top
  | .int n, .int m => f n m

instance : Add Integers where
  add x y := map_int x y
    fun n m => .int (n + m)

instance : Sub Integers where
  sub x y := map_int x y
    fun n m => .int (n - m)

instance : Mul Integers where
  mul x y := match x, y with
  | .bot, _ | _, .bot => .bot
  | .int 0, _ | _, .int 0 => .int 0
  | .top, _ | _, .top => .top
  | .int n, .int m => .int (n * m)

  instance : ToString Integers where
    toString x := match x with
    | .bot => "⊥"
    | .top => "⊤"
    | .int n => toString n

instance: ValueDomain Integers where
  new := .int 0
  from_const := .int
  rand a b := if a = b then .int a else .top
  widen _ a b := match a, b with
  | .bot, c | c, .bot => c
  | .int n, .int m => if n = m then .int n else .top
  | _, _ => .top
  narrow _ a b := match a, b with
  | .bot, c | c, .bot => c
  | .int n, .int m => if n = m then .int n else .top
  | _, _ => .top
  subset_dec := sorry
  is_bot_dec := sorry
