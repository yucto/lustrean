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
  variable {α : Type} [ι : BoundedLattice α]

  attribute [simp] bot top join meet
  attribute [simp]
  join_commutative join_associative
  join_absorption join_bot join_top
  meet_commutative meet_associative
  meet_absorption meet_bot meet_top

  @[simp]
  def is_bot : α → Prop :=
    (· = ι.bot)

  @[simp]
  def is_subset : α → α → Prop :=
    fun x y => x = ι.meet x y

  def is_increasing : (Nat → α) → Prop :=
    fun x => ∀ (n : Nat), is_subset (x n) (x (.succ n))

  def is_decreasing : (Nat → α) → Prop :=
    fun x => ∀ (n : Nat), is_subset (x (.succ n)) (x n)

  @[simp]
  def join_idempotent : ∀ (x : α), ι.join x x = x :=
  by
    intros x
    conv =>
      lhs
      arg 2
      rw [←meet_top x]
    apply join_absorption

  @[simp]
  def meet_idempotent : ∀ (x : α), ι.meet x x = x :=
  by
    intros x
    conv =>
      lhs
      arg 2
      rw [←join_bot x]
    apply meet_absorption
end BoundedLattice

class Widen (α : Type) where
  -- Nat : number of iterations
  widen : α → α → Nat → α

namespace Widen
  variable {α : Type} [Widen α]

  @[simp]
  def widen_seq (x : Nat → α) (n : Nat) : α := match n with
  | 0 => x 0
  | .succ n => Widen.widen (widen_seq x n) (x n.succ) n
end Widen

class WidenLawful (α : Type)
extends Widen α, BoundedLattice α
where
  covering_left : ∀  (x y : α) (n : Nat), BoundedLattice.is_subset x (widen x y n)
  covering_right : ∀  (x y : α) (n : Nat), BoundedLattice.is_subset y (widen x y n)
  -- trust Adrien for termination

attribute [simp] WidenLawful.covering_left WidenLawful.covering_right

class Narrow (α : Type) where
  -- Nat : number of iterations
  narrow : α → α → Nat → α

namespace Narrow
  variable {α : Type} [Narrow α]

  @[simp]
  def narrow_seq (x : Nat → α) (n : Nat) : α := match n with
  | 0 => x 0
  | .succ n => Narrow.narrow (narrow_seq x n) (x n.succ) n
end Narrow

class NarrowLawful (α : Type)
extends Narrow α, BoundedLattice α
where
  bounding_low : ∀  (x y : α) (n : Nat),
    BoundedLattice.is_subset (BoundedLattice.meet x y) (narrow x y n)
  bounding_high : ∀  (x y : α) (n : Nat),
    BoundedLattice.is_subset (narrow x y n) x
  -- trust Adrien for termination

attribute [simp] NarrowLawful.bounding_low NarrowLawful.bounding_high

class Domain (α : Type)
extends Add α, Mul α, Sub α, BoundedLattice α,
  ToString α, WidenLawful α, NarrowLawful α
where
  new : α
  eq_dec : DecidableEq α
  -- TODO: guard, assign

attribute [simp] Domain.eq_dec
