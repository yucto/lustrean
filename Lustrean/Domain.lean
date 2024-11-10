class BoundedLattice (α : Type) where
  bot : α
  top : α
  join : α → α → α
  meet : α → α → α
  join_commutative : ∀ (x y : α), join x y = join y x
  join_associative : ∀ (x y z : α), join (join x y) z = join x (join y z)
  join_absorption : ∀ (x y : α), join x (meet x y) = x
  join_bot : ∀ (x : α), join x bot = x
  join_top : ∀ (x : α), join x top = top
  meet_commutative : ∀ (x y : α), meet x y = meet y x
  meet_associative : ∀ (x y z : α), meet (meet x y) z = meet x (meet y z)
  meet_absorption : ∀ (x y : α), meet x (join x y) = x
  meet_top : ∀ (x : α), meet x top = x
  meet_bot : ∀ (x : α), meet x bot = bot

namespace BoundedLattice
  def is_bot {α : Type} [ι : BoundedLattice α] : α → Prop :=
    (· = ι.bot)

  def is_subset {α : Type} [ι : BoundedLattice α] : α → α → Prop :=
    fun x y => x = ι.meet x y

  def is_increasing {α : Type} [BoundedLattice α] : (Nat → α) → Prop :=
    fun x => ∀ (n : Nat), is_subset (x n) (x (.succ n))

  def is_decreasing {α : Type} [BoundedLattice α] : (Nat → α) → Prop :=
    fun x => ∀ (n : Nat), is_subset (x (.succ n)) (x n)
end BoundedLattice

class Widen (α : Type)
extends BoundedLattice α
where
  -- Nat : number of iterations
  widen : α → α → Nat → α
  covering_left : ∀  (x y : α) (n : Nat), BoundedLattice.is_subset x (widen x y n)
  covering_right : ∀  (x y : α) (n : Nat), BoundedLattice.is_subset y (widen x y n)
  widen_termination : ∀ (x : Nat → α),
    BoundedLattice.is_increasing x →
    let y : Nat → α := Nat.recAux (x 0) (
      fun m y => widen y (x (.succ m)) (.succ m)
    )
    ∃ (n : Nat), y (.succ n) = y n

class Narrow (α : Type)
extends BoundedLattice α
where
  -- Nat : number of iterations
  narrow : α → α → Nat → α
  bounding_low : ∀  (x y : α) (n : Nat), BoundedLattice.is_subset x y ->
    BoundedLattice.is_subset x (narrow x y n)
  bounding_high : ∀  (x y : α) (n : Nat), BoundedLattice.is_subset x y ->
    BoundedLattice.is_subset (narrow x y n) y
  narrow_termination : ∀ (x : Nat → α),
    BoundedLattice.is_decreasing x →
    let y : Nat → α := Nat.recAux (x 0) (
      fun m y => narrow y (x (.succ m)) (.succ m)
    )
    ∃ (n : Nat), y (.succ n) = y n

class Domain (α : Type)
extends Add α, Mul α, Sub α, BoundedLattice α,
  ToString α, Widen α, Narrow α
where
  new : α
  eq_dec : DecidableEq α
  -- TODO: guard, assign

class ValueDomain (α : Type)
extends Add α, Mul α, Sub α, BoundedLattice α,
  ToString α, Widen α, Narrow α
where
  new : α
  from_const : Int → α
  -- interval [a, b]
  rand : Int → Int → α
  eq_dec : DecidableEq α
  -- TODO: backward operations, comparisons

-- TODO:
-- constants, intervals, build a non-relational domain from value domains

-- TODO:
-- should the classes be parameterized by the constants and variables
-- of the program, or should it go into the type ?
