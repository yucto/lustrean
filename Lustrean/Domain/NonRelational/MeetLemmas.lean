import Lustrean.Domain.NonRelational.Basic

namespace Lustrean.NonRelational
variable {α : Type} {n : Nat} [BEq α]
variable [ι : ValueDomain α]
variable (x y z : NonRelational α n)

theorem meet_commutative : meet x y = meet y x := by
  cases x <;> cases y <;> simp [meet, map2Nil, coalesce]
  rename_i x y
  simp [BoundedLattice.meet_commutative]

theorem meet_associative : meet (meet x y) z = meet x (meet y z) := by
  match x with
  | .bot => simp [meet, map2Nil]
  | .non_rel ⟨x, x_prop⟩ =>
  match y with
  | .bot => simp [meet, map2Nil]
  | .non_rel ⟨y, y_prop⟩ =>
  match z with
  | .bot => simp [meet, map2Nil]
  | .non_rel ⟨z, z_prop⟩ =>
  simp only [meet, map2Nil, coalesce]
  simp only [Vector.get_of_fn_fin]
  if h : ∀ i : Fin n, x.get i ⊓ y.get i ⊓ z.get i ≠ ⊥ then
    have: ∀ i : Fin n, x.get i ⊓ y.get i ≠ ⊥ := by
      grind [BoundedLattice.meet_associative, BoundedLattice.meet_commutative, BoundedLattice.meet_bot]
    have: ∀ i : Fin n, y.get i ⊓ z.get i ≠ ⊥ := by
      grind [BoundedLattice.meet_associative, BoundedLattice.meet_commutative, BoundedLattice.meet_bot]
    simp [*]
  else
    by_cases ∀ i: Fin n, x.get i ⊓ y.get i ≠ ⊥ <;>
    by_cases ∀ i : Fin n, y.get i ⊓ z.get i ≠ ⊥ <;>
    simp [*]

@[simp]
theorem _root_.Vector.ofFn_get_self{α: Type}{n: Nat}(v: Vector α n)
: Vector.ofFn (fun i => v.get i) = v
:= by ext; simp [getElem]

theorem meet_absorption : meet x (join x y) = x := by
  match x, y with
  | .bot, _ =>
    simp [meet, map2Nil]
  | .non_rel ⟨x, x_prop⟩, .bot =>
    simp [join, meet, map2Nil, coalesce, BoundedLattice.meet_idempotent, *]
  | .non_rel ⟨x, x_prop⟩, .non_rel ⟨y, y_prop⟩ =>
    simp [meet, map2Nil, join, coalesce, *]

theorem meet_top : x.meet top = x := by
  match x with
  | .bot => simp [meet, map2Nil]
  | .non_rel ⟨x, x_prop⟩ =>
    simp [meet, map2Nil, coalesce, top, *]

theorem meet_bot : x.meet bot = bot := by
  cases x <;> simp [meet, map2Nil]
end Lustrean.NonRelational
