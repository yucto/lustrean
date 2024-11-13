import Lustrean.Domain.Domain

class ValueDomain (α : Type)
extends Add α, Mul α, Sub α, BoundedLattice α,
  ToString α, WidenLawful α, NarrowLawful α
where
  new : α
  from_const : Int → α
  -- interval [a, b]
  rand : Int → Int → α
  eq_dec : DecidableEq α
  -- TODO: backward operations, comparisons

structure NonRelational (α : Type) [ValueDomain α] (n : Nat)
where
  env : Fin n → α

namespace NonRelational
  variable (α : Type) (n : Nat)
  variable [ι : ValueDomain α]

  instance : Add (NonRelational α n) where
    add x y := NonRelational.mk
      fun i => ι.add (x.env i) (y.env i)

  instance : Sub (NonRelational α n) where
    sub x y := NonRelational.mk
      fun i => ι.sub (x.env i) (y.env i)

  instance : Mul (NonRelational α n) where
    mul x y := NonRelational.mk
      fun i => ι.mul (x.env i) (y.env i)

  instance : ToString (NonRelational α n) where
    toString x :=
      let rec acc (i : Nat) : String := match i with
      | 0 => ""
      | 1 => if h : i < n
        then
          let v := x.env (Fin.mk i h)
          s!"{v}"
        else ""
      | .succ i => if h : i < n
        then
          let r := acc i
          let v := x.env (Fin.mk i h)
          s!"{r} ; {v}"
        else acc i
      let r := acc n
      s!"[ {r} ]"

  instance : BoundedLattice (NonRelational α n) where
    bot := NonRelational.mk
      fun _ => ι.bot
    top := NonRelational.mk
      fun _ => ι.top
    join x y := NonRelational.mk
      fun i => ι.join (x.env i) (y.env i)
    meet x y := NonRelational.mk
      fun i => ι.meet (x.env i) (y.env i)
    join_commutative := by simp
    join_associative := by simp
    join_absorption := by simp
    join_bot := by
      intros x
      cases x <;> simp
    join_top := by
      intros x
      cases x <;> simp
    meet_commutative := by simp
    meet_associative := by simp
    meet_absorption := by simp
    meet_top := by
      intros x
      cases x <;> simp
    meet_bot := by
      intros x
      cases x <;> simp

  instance : Widen (NonRelational α n) where
    widen x y n := NonRelational.mk
      fun i => ι.widen (x.env i) (y.env i) n

  instance : WidenLawful (NonRelational α n) where
    covering_left := by
      intros x y n
      simp
      cases x <;> simp
      funext
      apply ι.covering_left
    covering_right := by
      intros x y n
      simp
      cases y <;> simp
      funext
      apply ι.covering_right

  instance : Narrow (NonRelational α n) where
    narrow x y n := NonRelational.mk
      fun i => ι.narrow (x.env i) (y.env i) n

  instance : NarrowLawful (NonRelational α n) where
    bounding_low := by
      intros x y n
      simp [-BoundedLattice.meet_associative]
      funext
      apply ι.bounding_low
    bounding_high := by
      intros x y n
      simp [-BoundedLattice.meet_commutative, Narrow.narrow]
      funext
      apply ι.bounding_high

  instance : DecidableEq (NonRelational α n) := fun x y => by
    cases x <;> cases y <;> rename_i env env'
    simp
    rw [funext_iff]
    induction n
    · apply Decidable.isTrue
      intros i
      cases i
      rename_i h
      cases h
    · rename_i n IH
      let restrict (f : Fin (n + 1) → α) (i : Fin n) : α := f i.succ
      cases (IH (restrict env) (restrict env')) <;> rename_i H
      · apply Decidable.isFalse
        intros Hc
        apply H
        intros i
        cases i <;> rename_i n Hi
        simp [restrict]
        apply Hc
      · let zero : Fin (n + 1) := Fin.mk 0 (Nat.zero_lt_succ n)
        let HD := ι.eq_dec (env zero) (env' zero)
        cases HD <;> rename_i H0
        · apply Decidable.isFalse
          intros Hc
          apply H0
          apply Hc
        · apply Decidable.isTrue
          apply Fin.cases <;> assumption

  instance : Domain (NonRelational α n) where
    new := NonRelational.mk fun _ => ValueDomain.new
    eq_dec := inferInstance
    -- TODO: pourquoi ça n'infère pas ??
    covering_left := WidenLawful.covering_left
    covering_right := WidenLawful.covering_right

    bounding_low := NarrowLawful.bounding_low
    bounding_high := NarrowLawful.bounding_high
end NonRelational
