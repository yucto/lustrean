import Lustrean.Domain.NonRelational
import Lustrean.Domain.GaloisConnection
import Mathlib.Order.Defs.PartialOrder
import Mathlib.Data.Set.Defs
import Mathlib.Algebra.Group.Pointwise.Set.Basic

namespace Lustrean.Domain

attribute [local simp] Int.compare_eq_gt Int.compare_eq_lt
private def Int.compare_eq_of_lt a b := @Int.compare_eq_lt a b  |>.mpr
local grind_pattern Int.compare_eq_of_lt => compare a b
private def Int.compare_eq_of_eq a b := @Int.compare_eq_eq a b  |>.mpr
local grind_pattern Int.compare_eq_of_eq => compare a b
private def Int.compare_eq_of_gt a b := @Int.compare_eq_gt a b  |>.mpr
local grind_pattern Int.compare_eq_of_gt => compare a b


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

instance: Std.ToFormat Sign where format := fun
|.mk false false false => "[⊥]"
|.mk true  false false => "[=0]"
|.mk false true  false => "[>0]"
|.mk false false true  => "[<0]"
|.mk true  true  false => "[≥0]"
|.mk true  false true  => "[≤0]"
|.mk false true  true  => "[≠0]"
|.mk true  true  true  => "[⊤]"
instance: ToString Sign := ⟨toString ∘ Std.format⟩
instance: Repr Sign := ⟨fun a _ => Std.format a⟩

namespace Notation
scoped notation "[⊥]" => Sign.None
scoped notation "[⊤]" => Sign.All
scoped notation "[=0]" => Sign.Zero
scoped notation "[>0]" => Sign.Pos
scoped notation "[<0]" => Sign.Neg
scoped notation "[≥0]" => Sign.ZeroPos
scoped notation "[≤0]" => Sign.ZeroNeg
end Notation

def join(a b: Sign): Sign where
  hasZero := a.hasZero || b.hasZero
  hasPos  := a.hasPos  || b.hasPos
  hasNeg  := a.hasNeg  || b.hasNeg

def meet(a b: Sign): Sign where
  hasZero := a.hasZero && b.hasZero
  hasPos  := a.hasPos  && b.hasPos
  hasNeg  := a.hasNeg  && b.hasNeg

def add(a b : Sign): Sign :=
  if a = .None ∨ b = .None then
    .None
  else
    {
      hasZero := a.hasZero && b.hasZero ||
                 a.hasNeg  && b.hasPos  ||
                 a.hasPos  && b.hasNeg
      -- Safe since we assume the other is non-empty
      hasPos  := a.hasPos  || b.hasPos
      -- Safe since we assume the other is non-empty
      hasNeg  := a.hasNeg  || b.hasNeg
    }

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

def sub(a b: Sign): Sign :=
  a.add b.neg

def div(a b: Sign): Sign :=
  if b = .Zero then
    .None
  else {
    hasZero := a.hasZero,
    hasPos  := a.hasPos && b.hasPos || a.hasNeg && b.hasNeg
    hasNeg  := a.hasNeg && b.hasPos || b.hasNeg && b.hasPos
  }

@[grind]
def incl(a b: Sign): Bool :=
  !(a.hasZero && !b.hasZero) &&
  !(a.hasPos  && !b.hasPos ) &&
  !(a.hasNeg  && !b.hasNeg )

end Sign

instance: Add Sign := .mk Sign.add
instance: Mul Sign := .mk Sign.mul
instance: Neg Sign := .mk Sign.neg
instance: Sub Sign := .mk Sign.sub
instance: Div Sign := .mk Sign.div
instance: Widen Sign  where widen a b _ := a.join b
instance: Narrow Sign where narrow a b _ := a.meet b

section GaloisEmbedding
namespace Sign

/-! Inclusion of Sign elements establishes a partial order -/

@[grind =]
instance instLE: LE Sign where
  le x y := Sign.incl x y = true

@[grind]
instance instPartialOrderSign: PartialOrder Sign where
  le_refl := by simp [LE.le, Sign.incl]
  le_trans := by
    intros; simp only [LE.le] at *; grind [Sign.incl]
  le_antisymm := by
    rintro ⟨z1,p1,n1⟩ ⟨x2,p2,n2⟩ ab bc
    simp only [LE.le, incl, Bool.not_and, Bool.not_not, Bool.and_eq_true, Bool.or_eq_true,
      Bool.not_eq_eq_eq_not, Bool.not_true, mk.injEq] at *
    grind

open Classical in
/--
  Abstraction of a set of integers by `Sign` (which only captures
  its element's signature (<0,=0,>0) information)

  Since we make no assumption of whether our sets are decidable or
  not, we must use the axiom of choice to decide the conditions
  `∃ z ∈ X, z > 0` and `∃ z ∈ X, z > 0`. This makes our abstract
  function noncomputable, but it is acceptable since we only make
  use of it to prove theorems about our operators.
-/
@[grind =]
noncomputable def abstract(X: Set Int): Sign := {
      hasZero := 0 ∈ X
      hasPos := ∃ z ∈ X, z > 0
      hasNeg := ∃ z ∈ X, z < 0
}

/-- The integer set represented by a particular `Sign` element -/
@[grind =]
def concrete(a: Sign): Set Int := setOf λ z ↦
  match compare z 0 with
  | .lt => a.hasNeg
  | .eq => a.hasZero
  | .gt => a.hasPos

/--
  There is a Galois embedding between the Sign domain and the
  Integers subset domain.
-/
def gc: GaloisConnection Sign.abstract Sign.concrete := by
    rintro X ⟨p,z,n⟩
    constructor <;> grind [LE.le]

-- TODO: It'd be nice if there was a simproc that propagated
-- equalities down `match` statements.

noncomputable
instance ge: GaloisEmbedding abstract concrete := gc.toGaloisInsertion <| by
  rintro ⟨hasPos, z, hasNeg⟩
  simp [Sign.abstract, Sign.concrete, LE.le, Sign.incl]
  apply And.intro
  · if h: hasPos then apply Or.inr; exists 1  else grind
  · if h: hasNeg then apply Or.inr; exists -1 else grind

end Sign
end GaloisEmbedding

section Theorems
namespace Sign

theorem join_commutative(a b: Sign): a.join b = b.join a := by
  have h: ∀ (a b: Sign), a.join b ≤ b.join a := by
    intros a b
    apply Sign.ge.u_le_u_iff.mp
    intros x
    grind [Sign.join]
  grind [Std.IsPartialOrder.le_antisymm]

theorem join_associative (a b c: Sign): (a.join b).join c = a.join (b.join c) := by
  apply Std.IsPartialOrder.le_antisymm
  all_goals (
    apply Sign.ge.u_le_u_iff.mp
    intros p
    grind [Sign.join]
  )

theorem meet_commutative(a b: Sign): a.meet b = b.meet a := by
  have h: ∀ (a b: Sign), a.meet b ≤ b.meet a := by
    intros a b
    apply Sign.ge.u_le_u_iff.mp
    intros x
    grind [Sign.meet]
  grind [Std.IsPartialOrder.le_antisymm]

theorem meet_associative(a b c: Sign): (a.meet b).meet c = a.meet (b.meet c) := by
  apply Std.IsPartialOrder.le_antisymm
  all_goals(
    apply Sign.ge.u_le_u_iff.mp
    intros p
    grind [Sign.meet]
  )

theorem join_absorption: ∀ (x y: Sign), x.join (x.meet y) = x:= by
  rintro ⟨z,p,n⟩ ⟨z',p',n'⟩
  grind [join, meet, mk.injEq, Bool.or_eq_left_iff_imp]

theorem meet_absorption: ∀ (x y: Sign), x.meet (x.join y) = x:= by
  rintro ⟨z,p,n⟩ ⟨z',p',n'⟩
  grind [meet, join, mk.injEq, Bool.and_eq_left_iff_imp]

end Sign
end Theorems

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

  rand := fun
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

section Correctness

open Classical in
private noncomputable def Set.add(X Y: Set Int): Set Int
:= λ z ↦ ∃ x y, z = x + y ∧ X x = true ∧ Y y = true

theorem add_correct
: Sign.gc.IsBinAbstraction (· + ·) Sign.add
:= by
  rintro ⟨z,p,n⟩ ⟨z',p',n'⟩
  if h: ⟨z,p,n⟩ = Sign.None then
    obtain ⟨rfl, rfl, rfl⟩ := h
    intros e
    simp [Sign.add, Sign.None, concrete, Set.add]
    grind
  else if h: ⟨z',p',n'⟩ = Sign.None then
    obtain ⟨rfl, rfl, rfl⟩ := h
    intros e
    simp [Sign.add, Sign.None, concrete, Set.add]
    grind
  else
  intros e
  simp only [Set.add, Sign.add, decide_eq_true_eq]
  rintro ⟨e1,e2, e1_e2, x_e1, y_e2⟩
  cases com_e: compare e 0 <;> simp only [Int.compare_eq_eq, Int.compare_eq_lt, Int.compare_eq_gt] at com_e
  all_goals (
    simp only [ concrete ] at x_e1 y_e2 ⊢
    grind
  )
  -- ADD IS NOT COMPLETE!
  -- We have [<0] + [<0] = [<0]
  #eval open Sign.Notation in
    [<0] + [<0]
  -- but if -1 ∈ γ ([<0] + [<0]) then it doesn't mean -1 ∈ (γ[<0] + γ[<0])).
  -- In particular, -1 ∈ γ(a) + γ(b) → ∃ c ≥ 0 ∈ γ(a) ∪ γ(b), since -1 cannot
  -- be obtained from the sum of two negative integers.
end Correctness
