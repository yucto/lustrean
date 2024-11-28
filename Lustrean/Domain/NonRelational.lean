import Lustrean.Domain.Domain

class ValueDomain (α : Type)
extends Add α, Neg α, Mul α, Sub α, Div α, BoundedLattice α,
  ToString α, WidenLawful α, NarrowLawful α
where
  new : α
  from_const : Int → α
  -- interval [a, b]
  rand : Int → Int → α
  eq_dec : DecidableEq α
  -- compare op x y = (x', y') where
  -- x' = { v ∈ x | ∃ v' ∈ y, v op v' }
  -- y' = { v' ∈ y | ∃ v ∈ x, v op v' }
  compare : compare_op → α → α → α × α

namespace ValueDomain
  variable (α : Type) [ValueDomain α]
  -- backward operations :
  -- backward_op x y r = (x', y') where
  -- x' = { v ∈ x | ∃ v' ∈ y, v op v' ∈ r }
  -- y' = { v' ∈ y | ∃ v ∈ x, v op v' ∈ r }
  def backward_neg (x r : α) : α := BoundedLattice.meet (Neg.neg r) x

  def backward_add (x y r : α) : α × α :=
    (BoundedLattice.meet x (Sub.sub r y), BoundedLattice.meet y (Sub.sub r x))

  def backward_sub (x y r : α) : α × α :=
    (BoundedLattice.meet x (Add.add r y), BoundedLattice.meet y (Sub.sub x r))

  def backward_mul (x y r : α) : α × α :=
    (BoundedLattice.meet x (Div.div r y), BoundedLattice.meet y (Div.div r x))

  def backward_div (x y r : α) : α × α :=
    (BoundedLattice.meet x (Mul.mul r y), BoundedLattice.meet y (Div.div x r))
end ValueDomain

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

  instance : Div (NonRelational α n) where
    div x y := NonRelational.mk
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

  def update (x : NonRelational α n) (i : Fin n) (a : α) :
    NonRelational α n
  :=
    NonRelational.mk fun j => if i = j then a else x.env j

  def eval (x : NonRelational α n) (e : iexpr n) : α :=
  match e with
  | .var i => x.env i
  | .rand a b => ι.rand a b
  | .const n => ι.from_const n
  | .neg e => - eval x e
  | .binop e₁ op e₂ =>
    let i₁ := eval x e₁
    let i₂ := eval x e₂
    match op with
    | .iadd => i₁ + i₂
    | .isub => i₁ - i₂
    | .imul => i₁ * i₂
    | .idiv => i₁ / i₂

  def assign (x : NonRelational α n) (i : Fin n) (e : iexpr n) :
    NonRelational α n
  :=
    update α n x i (eval α n x e)

  def backward_eval (x : NonRelational α n) (e : iexpr n) (r : α) :
    NonRelational α n
  :=
    let _ : DecidableEq α := ι.eq_dec -- help class inference
    match e with
    | .var i => update α n x i (ι.meet (x.env i) r)
    | .rand a b => if ι.is_bot (ι.meet r (ι.rand a b))
      then BoundedLattice.bot
      else x
    | .const n => if ι.is_bot (ι.meet r (ι.from_const n))
      then BoundedLattice.bot
      else x
    | .neg e =>
      let i := eval α n x e
      let r := ι.backward_neg i r
      backward_eval x e r
    | .binop e₁ op e₂ =>
      let i₁ := eval α n x e₁
      let i₂ := eval α n x e₂
      let (r₁, r₂) := match op with
      | .iadd => ι.backward_add i₁ i₂ r
      | .isub => ι.backward_sub i₁ i₂ r
      | .imul => ι.backward_mul i₁ i₂ r
      | .idiv => ι.backward_div i₁ i₂ r
      BoundedLattice.meet (backward_eval x e₁ r₁) (backward_eval x e₂ r₂)

  def guard (x : NonRelational α n) (b : bexpr n) :
    NonRelational α n
  := match b with
  | .random | .const true => x
  | .const false => BoundedLattice.bot
  | .compare e₁ op e₂ =>
    let i₁ := eval α n x e₁
    let i₂ := eval α n x e₂
    let (r₁, r₂) := ι.compare op i₁ i₂
    BoundedLattice.meet (backward_eval α n x e₁ r₁) (backward_eval α n x e₂ r₂)
  | .or b₁ b₂ => BoundedLattice.join (guard x b₁) (guard x b₂)
  | .and b₁ b₂ => BoundedLattice.meet (guard x b₁) (guard x b₂)

  instance : Domain (NonRelational α n) where
    new := NonRelational.mk fun _ => ValueDomain.new
    nb_var := n
    eq_dec := inferInstance
    assign := assign α n
    guard := guard α n
    -- TODO: pourquoi ça n'infère pas ??
    covering_left := WidenLawful.covering_left
    covering_right := WidenLawful.covering_right

    bounding_low := NarrowLawful.bounding_low
    bounding_high := NarrowLawful.bounding_high
end NonRelational
