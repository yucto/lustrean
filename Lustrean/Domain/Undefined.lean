import Aesop
import Lustrean.Domain.NonRelational

structure Undefined (α : Type) : Type where
  val : α
  may_be_nil : Bool

namespace Undefined
  variable {α : Type} [ι : ValueDomain α] (x y z : Undefined α)

  def add : Undefined α := .mk (x.val + y.val) (x.may_be_nil || y.may_be_nil)
  def neg : Undefined α := .mk (-x.val) (x.may_be_nil)
  def sub : Undefined α := .mk (x.val - y.val) (x.may_be_nil || y.may_be_nil)
  def mul : Undefined α := .mk (x.val * y.val) (x.may_be_nil || y.may_be_nil)
  def div : Undefined α := .mk (x.val / y.val) (x.may_be_nil || y.may_be_nil)

  instance : Add (Undefined α) where
    add := add
  instance : Neg (Undefined α) where
    neg := neg
  instance : Sub (Undefined α) where
    sub := sub
  instance : Mul (Undefined α) where
    mul := mul
  instance : Div (Undefined α) where
    div := div

  def toString := if x.may_be_nil then ι.toString x.val
    else s!"{x.val} ⊔ nil"

  instance : ToString (Undefined α) where
    toString := toString

  def bot : Undefined α := .mk ⊥ false
  def top : Undefined α := .mk ⊤ true
  def meet : Undefined α := .mk (x.val ⊓ y.val) (x.may_be_nil && y.may_be_nil)
  def join : Undefined α := .mk (x.val ⊔ y.val) (x.may_be_nil || y.may_be_nil)

  instance : BoundedLattice (Undefined α) where
    bot := bot
    top := top
    meet := meet
    join := join
    join_commutative := sorry
    join_associative := sorry
    join_absorption := sorry
    join_bot := sorry
    join_top := sorry
    meet_commutative := sorry
    meet_associative := sorry
    meet_absorption := sorry
    meet_top := sorry
    meet_bot := sorry
    non_trivial := sorry

  def widen (n : Nat) : Undefined α :=
    .mk (ι.widen x.val y.val n) (x.may_be_nil || y.may_be_nil)
  def narrow (n : Nat) : Undefined α :=
    .mk (ι.narrow x.val y.val n) (x.may_be_nil && y.may_be_nil)

  instance : Widen (Undefined α) where
    widen := widen
  instance : Narrow (Undefined α) where
    narrow := narrow
  instance : WidenLawful (Undefined α) where
    covering_left := by
      intros x y n
      let ⟨x, b⟩ := x
      let ⟨y, b'⟩ := y
      unfold BoundedLattice.is_subset
      simp [Widen.widen, widen, meet]
      constructor
      · apply WidenLawful.covering_left
      · intros <;> left <;> assumption
    covering_right := by
      intros x y n
      let ⟨x, b⟩ := x
      let ⟨y, b'⟩ := y
      unfold BoundedLattice.is_subset
      simp [Widen.widen, widen, meet]
      constructor
      · apply WidenLawful.covering_right
      · intros <;> right <;> assumption
  instance : NarrowLawful (Undefined α) where
    bounding_low := by
      intros x y n
      let ⟨x, b⟩ := x
      let ⟨y, b'⟩ := y
      unfold BoundedLattice.is_subset
      simp [Narrow.narrow, narrow, meet]
      rw [←ι.meet_associative]
      apply NarrowLawful.bounding_low
    bounding_high := by
      intros x y n
      let ⟨x, b⟩ := x
      let ⟨y, b'⟩ := y
      unfold BoundedLattice.is_subset
      simp [Narrow.narrow, narrow, meet]
      constructor
      · apply NarrowLawful.bounding_high
      · intros <;> assumption

  instance : DecidableEq (Undefined α) :=
    fun x y =>
    let _ := ι.eq_dec
    if h : (x.val = y.val) ∧ (x.may_be_nil = y.may_be_nil)
    then .isTrue <| by
      cases x <;> cases y <;> simp at * <;> assumption
    else .isFalse <| by
      intro Hc
      apply h
      rw [Hc]
      simp

  def compare (op : compare_op) (x y : Undefined α) :
    Undefined α × Undefined α
  :=
    let (x', y') := ι.compare op x.val y.val
    (.mk x' x.may_be_nil, .mk y' y.may_be_nil)

  instance : ValueDomain (Undefined α) where
    new := .mk ι.new false
    from_const n := .mk (ι.from_const n) false
    rand a b := .mk (ι.rand a b) false
    nil := .mk ⊥ true
    eq_dec := inferInstance
    compare := compare
    covering_left := WidenLawful.covering_left
    covering_right := WidenLawful.covering_right

    bounding_low := NarrowLawful.bounding_low
    bounding_high := NarrowLawful.bounding_high
end Undefined
