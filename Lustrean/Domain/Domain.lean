import Aesop
import Lustrean.Imp

namespace Lustrean
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
  non_trivial : top ≠ bot
export BoundedLattice (bot top join meet)

notation " ⊤ " => top
notation " ⊥ " => bot
infixr:60 " ⊔ " => join
infixr:70 " ⊓ " => meet

namespace BoundedLattice
  variable {α : Type} [ι : BoundedLattice α]

  attribute [simp] bot top join meet
  attribute [simp]
  join_associative join_absorption join_bot join_top
  meet_associative meet_absorption meet_bot meet_top

  def is_bot : α → Prop :=
    (· = ⊥)

  def is_subset : α → α → Prop :=
    fun x y => x = meet x y

  infixr:50 " ⊑ " => is_subset

  theorem trans : ∀ {x y z : α}, x ⊑ y → y ⊑ z → x ⊑ z := by
    intros x y z Hx Hy
    unfold is_subset at *
    rw [Hx]
    conv =>
      lhs
      rw [Hy]
    rw [meet_associative]

  instance {α : Type} [ι : BoundedLattice α] : Trans (@is_subset α ι) (@is_subset α ι) (@is_subset α ι) where
    trans := trans

  theorem bot_min : ∀ {x : α}, ⊥ ⊑ x := by
    intros x
    unfold is_subset
    simp [meet_commutative]

  theorem antisymm : ∀ {x y : α}, x ⊑ y → y ⊑ x → x = y := by
    intros x y H H'
    unfold is_subset at *
    rw [meet_commutative] at H'
    rw [H]
    symm
    assumption

  instance {α : Type} [ι : BoundedLattice α] : Antisymm (@is_subset α ι) where
    antisymm := antisymm

  @[simp]
  theorem min_bot_is_bot : ∀ {x : α}, x ⊑ ⊥ → x = bot := by
    intros x H
    apply antisymm <;> [
      assumption ;
      apply bot_min
    ]

  theorem min_join_left : ∀ {x y : α}, x ⊑ x ⊔ y := by
    intros x y
    unfold is_subset
    symm
    apply meet_absorption

  theorem min_join_right : ∀ {x y : α}, y ⊑ x ⊔ y := by
    intros
    rw [join_commutative]
    apply min_join_left

  theorem join_eq_bot_iff_bot : ∀ {x y : α}, x ⊔ y = ⊥ ↔ x = ⊥ ∧ y = ⊥ := by
    intros x y
    constructor
    · intros H
      have : ∀ (a b : α), a ⊔ b = ⊥ → a = ⊥ := by
        intros a b Ha
        have : a = a ⊓ (a ⊔ b) := by simp
        rw [this, Ha]
        simp
      constructor <;> apply this <;> first | assumption | rw [join_commutative] <;> assumption
    · intro ⟨ Hx, Hy ⟩
      simp [Hx, Hy]

  theorem meet_not_bot_left : ∀ {x y : α}, x ⊓ y ≠ ⊥ → x ≠ ⊥ := by
    intros x y H Hc
    apply H
    rw [Hc, meet_commutative]
    simp

  theorem meet_not_bot_right : ∀ {x y : α}, x ⊓ y ≠ ⊥ → y ≠ ⊥ := by
    intros x y H Hc
    apply H
    rw [Hc]
    simp

  instance is_bot_dec [DecidableEq α] : DecidablePred (@is_bot α ι) := by
    rename_i ι'
    intros _
    apply ι'

  instance is_subset_dec [DecidableEq α] : DecidableRel (@is_subset α ι) := by
    rename_i ι'
    intros _ _
    apply ι'

  def is_increasing : (Nat → α) → Prop :=
    fun x => ∀ n, x n ⊑ x (n+1)

  def is_decreasing : (Nat → α) → Prop :=
    fun x => ∀ n, x (n+1) ⊑ x n

  @[simp]
  theorem join_idempotent : ∀ x : α, x ⊔ x = x := by
    intros x
    conv =>
      lhs
      arg 2
      rw [←meet_top x]
    apply join_absorption

  @[simp]
  theorem meet_idempotent : ∀ x : α, x ⊓ x = x := by
    intros x
    conv =>
      lhs
      arg 2
      rw [←join_bot x]
    apply meet_absorption

  theorem refl : ∀ {x : α}, x ⊑ x := by
    intros x
    simp [is_subset]

  @[simp]
  theorem meet_min_left : ∀ {x y : α}, x ⊓ y ⊑ x := by
    intros x y
    simp [is_subset]
    conv =>
      rhs
      arg 2
      rw [meet_commutative]
    rw [←meet_associative]
    simp

  @[simp]
  theorem meet_min_right : ∀ {x y : α}, x ⊓ y ⊑ y := by
    intros x y
    rw [meet_commutative]
    apply meet_min_left

end BoundedLattice

class Widen (α : Type) where
  -- Nat : number of iterations
  widen : α → α → Nat → α
export Widen (widen)

macro l:term " ∇_" n:term:max r:term : term => ``(widen $l $r $n)

namespace Widen
  variable {α : Type} [Widen α]

  @[simp]
  def widen_seq (x : Nat → α) : Nat → α
  | 0 => x 0
  | .succ n => (widen_seq x n) ∇_n (x n.succ)
end Widen

class WidenLawful (α : Type)
extends Widen α, BoundedLattice α
where
  covering_left : ∀ (x y : α) n, x ⊑ (x ∇_n y)
  covering_right : ∀ (x y : α) n, y ⊑ (x ∇_n y)
  -- trust Adrien for termination

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
  bounding_low : ∀  (x y : α) (n : Nat), (x ⊓ y) ⊑ (narrow x y n)
  bounding_high : ∀  (x y : α) (n : Nat), (narrow x y n) ⊑ x
  -- trust Adrien for termination

class Domain (α : Type)
extends BoundedLattice α, ToString α,
  WidenLawful α, NarrowLawful α
where
  new : α
  nb_var : Nat
  eq_dec : DecidableEq α
  -- keep only elements satisfying the boolean expression
  guard : α → BExpr nb_var → α
  assign : α → Fin nb_var → IExpr nb_var → α
export Domain (guard assign)

instance (α : Type) [Domain α] : DecidableEq α := Domain.eq_dec
end Lustrean
