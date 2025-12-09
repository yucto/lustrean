import Lustrean.Domain.NonRelational
import Lustrean.Domain.GaloisConnection

namespace Lustrean.Domain

/-- Abstraction over sets of integers. The only
 information retained is the sign of the elements
 of the set.  -/
structure Sign where mk ::
 hasZero: Bool := false
 hasPos: Bool  := false
 hasNeg: Bool  := false
 deriving DecidableEq, Repr, Inhabited

namespace Sign
/-- Seeing elements in `Sign` as a set, the opposite -/
  def opposite(s: Sign): Sign where
    hasZero := ! s.hasZero
    hasPos := ! s.hasPos
    hasNeg := ! s.hasNeg

/-  We name all elements of the type.  -/
section elements
  def None: Sign := {}
  def Zero: Sign := {hasZero := true}
  def Pos: Sign := {hasPos := true}
  def Neg: Sign := {hasNeg := true}
  def NonZero: Sign := Zero.opposite
  def ZeroPos: Sign := Neg.opposite
  def ZeroNeg: Sign := Pos.opposite
  def All: Sign := None.opposite
end elements

  instance: ToString Sign where toString := fun
  |.mk false false false => "[⊥]"
  |.mk true  false false => "[=0]"
  |.mk false true  false => "[>0]"
  |.mk false false true  => "[<0]"
  |.mk true  true  false => "[≥0]"
  |.mk true  false true  => "[≤0]"
  |.mk false true  true  => "[≠0]"
  |.mk true  true  true  => "[⊤]"

  def add(a b : Sign): Sign where
    hasZero := a.hasZero || b.hasZero
    hasPos  := a.hasPos || b.hasPos
    hasNeg  := a.hasNeg || b.hasNeg

  def mul(a b : Sign): Sign :=
    if a = .Zero ∨ b = .Zero then
      .Zero
    else
      {
        hasZero := a.hasZero || b.hasZero,
        hasPos  := a.hasPos && b.hasPos || a.hasNeg && b.hasNeg
        hasNeg  := a.hasNeg && b.hasPos || b.hasNeg && b.hasPos
      }

  def neg(a: Sign): Sign := {
    a with
    hasNeg := a.hasPos
    hasPos := a.hasNeg
  }

  def sub(a b: Sign): Sign := a.add b.neg
  def div(a b: Sign): Sign :=
    if b = .Zero then
      .None
    else {
      hasZero := a.hasZero,
      hasPos  := a.hasPos && b.hasPos || a.hasNeg && b.hasNeg
      hasNeg  := a.hasNeg && b.hasPos || b.hasNeg && b.hasPos

    }

  def incl(a b: Sign): Bool :=
    !(a.hasZero && !b.hasZero) &&
    !(a.hasPos  && !b.hasPos ) &&
    !(a.hasNeg  && !b.hasNeg )

  def join(a b: Sign): Sign where
    hasZero := a.hasZero || b.hasZero
    hasPos  := a.hasPos  || b.hasPos
    hasNeg  := a.hasNeg  || b.hasNeg

  def meet(a b: Sign): Sign where
    hasZero := a.hasZero && b.hasZero
    hasPos  := a.hasPos  && b.hasPos
    hasNeg  := a.hasNeg  && b.hasNeg

end Sign

instance: Add Sign := .mk Sign.add
instance: Mul Sign := .mk Sign.mul
instance: Neg Sign := .mk Sign.neg
instance: Sub Sign := .mk Sign.sub
instance: Div Sign := .mk Sign.div
instance: Widen Sign  where widen a b _ := a.join b
instance: Narrow Sign where narrow a b _ := a.meet b

section GaloisEmbedding
  /-- The concrete domain of Sign is the set of (computable)
      subsets of integers. -/
  abbrev Set α := α → Bool

  /-- We establish a partial order on sets through inclusion -/
  protected instance: LE (Set Int) where
    le f g := ∀ x, f x -> g x
  protected instance: Std.IsPartialOrder (Set Int) where
    le_refl := by intros f g a; assumption
    le_trans := by intros f g h fg gh a fa; apply (gh _ (fg a fa))
    le_antisymm := by
      intros f g fg gf
      ext x
      specialize fg x
      specialize gf x
      cases h: (f x) <;> grind

  /-- Inclusion of Sign elements establishes a partial order -/
  instance: LE Sign where
    le x y := Sign.incl x y = true
  /-- Inclusion of Sign elements establishes a partial order -/
  instance: Std.IsPartialOrder Sign where
    le_refl := by simp [LE.le, Sign.incl]
    le_trans := by
      intros; simp [LE.le, Sign.incl] at *; grind
    le_antisymm := by
      rintro ⟨z1,p1,n1⟩ ⟨x2,p2,n2⟩ ab bc
      simp [LE.le, Sign.incl] at *
      grind

  attribute [local simp] Int.compare_eq_gt Int.compare_eq_lt

  open Classical in
  /--
    There is a Galois embedding between the Sign domain and the
    Integers subset domain.

    To define the abstraction function, one needs to be able to
    determine whether a positive (resp. negative) integer is in
    the set or not. This is generally undecidable, so we need to
    make use of the axiom of choice. This is acceptable, since
    we don't use the abstraction nor concretization functions in
    our computations, just to justify the laws of operators.
  -/
  noncomputable instance instGESignIntSet: GaloisEmbedding (A := Sign) (C := Set Int) where
    concrete a z := (z = 0 -> a.hasZero) ∧ (z > 0 -> a.hasPos) ∧ (z < 0 -> a.hasNeg)
    abstract X := {
      hasZero := X 0
      hasPos := ∃ z, z > 0 ∧ X z
      hasNeg := ∃ z, z < 0 ∧ X z
    }
    connection:= by
      rintro ⟨z,p,n⟩ X
      constructor
      · intros abs_lt x x_X
        simp at *
        simp [LE.le, Sign.incl] at abs_lt
        cases h: compare x 0 <;> simp at h <;> grind
      · intros conc_lt
        simp [LE.le, Sign.incl] at ⊢
        apply and_assoc.mpr
        have h0 := conc_lt 0; simp at h0
        apply And.intro
        · grind
        apply And.intro
        ·
          if h: ∃ x, 0 < x ∧ X x = true then
            obtain ⟨x, x_lt, Xx⟩ := h
            specialize conc_lt x Xx; simp [x_lt] at conc_lt
            obtain ⟨_,rfl,_⟩ := conc_lt
            simp
          else
            apply Or.inl
            simpa using h
        ·
          if h: ∃ x, x < 0 ∧ X x = true then
            obtain ⟨x, x_lt, Xx⟩ := h
            specialize conc_lt x Xx; simp [x_lt] at conc_lt
            obtain ⟨_,_,rfl⟩ := conc_lt
            simp
          else
            apply Or.inl
            simpa using h
    embedding := by
      rintro ⟨z,p,n⟩
      simp
      apply And.intro
      · cases p_def: p
        · simp; grind
        · simp; exists 1; grind
      · cases n_def: n
        · simp; grind
        · simp; exists -1; grind
end GaloisEmbedding

#check WidenLawful
section theorems
namespace Sign

  theorem join_commutative(a b: Sign): a.join b = b.join a := by
    have h: ∀ (a b: Sign), a.join b ≤ b.join a := by
      intros a b
      apply instGESignIntSet.lt_of_concrete_lt
      intros x
      simp [GaloisConnection.concrete, Sign.join]
      grind
    grind [Std.IsPartialOrder.le_antisymm]

  theorem join_associative (a b c: Sign): (a.join b).join c = a.join (b.join c) := by
    apply Std.IsPartialOrder.le_antisymm
    all_goals(
      apply instGESignIntSet.lt_of_concrete_lt
      intros p
      simp [GaloisConnection.concrete, Sign.join]
      grind
    )

  theorem meet_commutative(a b: Sign): a.meet b = b.meet a := by
    have h: ∀ (a b: Sign), a.meet b ≤ b.meet a := by
      intros a b
      apply instGESignIntSet.lt_of_concrete_lt
      intros x
      simp [GaloisConnection.concrete, Sign.meet]
      grind
    grind [Std.IsPartialOrder.le_antisymm]

  theorem meet_associative(a b c: Sign): (a.meet b).meet c = a.meet (b.meet c) := by
    apply Std.IsPartialOrder.le_antisymm
    all_goals(
      apply instGESignIntSet.lt_of_concrete_lt
      intros p
      simp [GaloisConnection.concrete, Sign.meet]
      grind
    )
  theorem join_absorption: ∀ (x y: Sign), x.join (x.meet y) = x:= by
    rintro ⟨z,p,n⟩ ⟨z',p',n'⟩
    simp [Sign.meet, Sign.join]
    grind
  theorem meet_absorption: ∀ (x y: Sign), x.meet (x.join y) = x:= by
    rintro ⟨z,p,n⟩ ⟨z',p',n'⟩
    simp [Sign.meet, Sign.join]
    grind

end Sign
end theorems

instance: BoundedLattice Sign where
  bot := .None
  top := .All
  join := Sign.join
  meet := Sign.meet
  join_bot := by simp [Sign.None, Sign.join]
  join_top := by simp [Sign.All, Sign.None, Sign.opposite,  Sign.join]
  meet_bot := by simp [Sign.None, Sign.meet]
  meet_top := by simp [Sign.All, Sign.None, Sign.opposite, Sign.meet]
  non_trivial := by decide
  join_commutative := Sign.join_commutative
  join_associative := Sign.join_associative
  meet_commutative := Sign.meet_commutative
  meet_associative := Sign.meet_associative
  join_absorption  := Sign.join_absorption
  meet_absorption  := Sign.meet_absorption

instance: WidenLawful Sign where
  /- NOTE: These theorems are inlined since they depend on
     definitions introduced by the `BoundedLattice` typeclass -/
  covering_left := by
    rintro x y -
    simp [BoundedLattice.IsSubset, Widen.widen]
    rewrite [Sign.meet_absorption]
    rfl

  /- NOTE: These theorems are inlined since they depend on
     definitions introduced by the `BoundedLattice` typeclass -/
  covering_right := by
    rintro x y -
    simp [BoundedLattice.IsSubset, Widen.widen]
    rewrite [Sign.join_commutative, Sign.meet_absorption]
    rfl

instance: NarrowLawful Sign where
  /- NOTE: These theorems are inlined since they depend on
     definitions introduced by the `BoundedLattice` typeclass -/
  bounding_high := by
    rintro ⟨z,p,n⟩ ⟨z',p',n'⟩ -
    simp [BoundedLattice.IsSubset, Narrow.narrow]
    grind [Sign.meet]

  /- NOTE: These theorems are inlined since they depend on
     definitions introduced by the `BoundedLattice` typeclass -/
  bounding_low := by
    simp [BoundedLattice.IsSubset, Narrow.narrow]
    grind [Sign.meet]

instance: ValueDomain Sign where
  eq_dec := inferInstance

  /- TODO: What laws must `nil` obey? -/
  nil := .All

  /- TODO: What laws must `compare` obey?
    (x', y') st x' = {e  ∈ x : ∃e' ∈ y, e op e'}
                y' = {e' ∈ y : ∃e  ∈ x, e op e'}
  -/
  /- TODO: Improve -/
  compare op x y := match op with
  | .eq  => (x.meet y, x.meet y)
  | .neq => (x.join (x.meet y).opposite, y.join (x.meet y).opposite)
  | .le  => (x, y)
  | .lt  => (x, y)
  | .ge  => (x, y)
  | .gt  => (x, y)

  rand
  | .some l, .some r =>
    if l ≤ r then
      {
        hasZero := l ≤ 0 ∧ 0 ≤ r,
        hasPos := 0 < r,
        hasNeg := l < 0
      }
    else .None
  | .none, .none => .All
  | .none, .some r =>
    {
      hasZero := true,
      hasPos := 0 < r,
      hasNeg := false
    }
  | .some l, .none =>
    {
      hasZero := true,
      hasPos := false,
      hasNeg := l < 0
    }
