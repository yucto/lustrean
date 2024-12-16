import Lustrean.Facts
import Lustrean.Domain.Domain

class ValueDomain (α : Type)
extends Add α, Neg α, Mul α, Sub α, Div α, BoundedLattice α,
  ToString α, WidenLawful α, NarrowLawful α
where
  new : α
  from_const : Int → α
  -- interval [a, b]
  rand : Int → Int → α
  nil : α
  eq_dec : DecidableEq α
  -- compare op x y = (x', y') where
  -- x' = { v ∈ x | ∃ v' ∈ y, v op v' }
  -- y' = { v' ∈ y | ∃ v ∈ x, v op v' }
  compare : CompareOp → α → α → α × α

namespace ValueDomain
  variable (α : Type) [ValueDomain α]
  -- backward operations :
  -- backward_op x y r = (x', y') where
  -- x' = { v ∈ x | ∃ v' ∈ y, v op v' ∈ r }
  -- y' = { v' ∈ y | ∃ v ∈ x, v op v' ∈ r }
  def backward_neg (x r : α) : α := -r ⊓ x

  def backward_add (x y r : α) : α × α :=
    (x ⊓ r - y, y ⊓ r - x)

  def backward_sub (x y r : α) : α × α :=
    (x ⊓ (Add.add r y), BoundedLattice.meet y (Sub.sub x r))

  def backward_mul (x y r : α) : α × α :=
    (x ⊓ r / y, y ⊓ r / x)

  def backward_div (x y r : α) : α × α :=
    (x ⊓ r * y, y ⊓ x / r)
end ValueDomain

inductive NonRelational (α : Type) [ValueDomain α] (n : Nat) :=
| non_rel : { env : Fin n → α // ∀ i, env i ≠ ⊥} → NonRelational α n
| bot : NonRelational α n

namespace NonRelational
  variable {α : Type} {n : Nat}
  variable [ι : ValueDomain α]
  variable (x y z : NonRelational α n)

  def coalesce (env : Fin n → α) : NonRelational α n :=
    let _ := fun i => ι.eq_dec (env i) ⊥
    if H : ∀ i, env i ≠ ⊥
    then .non_rel <| .mk env H
    else .bot

  def map_nil (f : (Fin n → α) → (Fin n → α)) : NonRelational α n :=
    match x with
    | .non_rel x => coalesce (f x.val)
    | .bot => .bot

  def map2_nil (f : (Fin n → α) → (Fin n → α) → (Fin n → α)) : NonRelational α n :=
    match x, y with
    | .non_rel x, .non_rel y => coalesce (f x.val y.val)
    | _, _ => .bot

  protected def add :=
    map2_nil x y fun x y i => x i + y i

  instance : Add (NonRelational α n) where
    add := NonRelational.add

  protected def neg :=
    map_nil x fun x i => -(x i)

  instance : Neg (NonRelational α n) where
    neg := NonRelational.neg

  protected def sub :=
    map2_nil x y fun x y i => x i - y i

  instance : Sub (NonRelational α n) where
    sub := NonRelational.sub

  protected def mul :=
    map2_nil x y fun x y i =>
      x i * y i

  instance : Mul (NonRelational α n) where
    mul := NonRelational.mul

  protected def div :=
    map2_nil x y fun x y i =>
      x i / y i

  instance : Div (NonRelational α n) where
    div := NonRelational.div

  protected def toString : NonRelational α n → String
  | .bot => "⊥"
  | .non_rel env =>
    let rec acc : Nat → String
    | 0 => ""
    | 1 => if h : 1 < n
      then
        let v := env.val (Fin.mk 1 h)
        s!"{v}"
      else ""
    | .succ i => if h : i < n
      then
        let r := acc i
        let v := env.val (Fin.mk i h)
        s!"{r} ; {v}"
      else acc i
    let r := acc n
    s!"[ {r} ]"

  instance : ToString (NonRelational α n) where
    toString := NonRelational.toString

  theorem join_neq_bot : ∀ (x y : { env : Fin n → α // ∀ i, env i ≠ ⊥}) i,
    x.val i ⊔ y.val i ≠ ⊥
  := by
    intros x y i
    let ⟨y, H⟩ := y
    simp [BoundedLattice.join_eq_bot_iff_bot]
    intros
    apply H

  def top : NonRelational α n := .non_rel <| .mk (fun _ => ι.top) fun _ => ι.non_trivial

  def join : NonRelational α n := match x, y with
    | .non_rel ⟨x, H⟩, .non_rel ⟨y, _⟩ =>
      .non_rel <| .mk (fun i => ι.join (x i) (y i)) <| by
        intros i
        simp [BoundedLattice.join_eq_bot_iff_bot, H]
    | .bot, z | z, .bot => z

  def meet : NonRelational α n := map2_nil x y fun x y =>
      fun i => ι.meet (x i) (y i)

  theorem join_commutative : join x y = join y x := by
    cases x <;> cases y <;> simp [join, coalesce]
    rename_i x y
    simp [BoundedLattice.join_commutative]

  theorem join_associative : join (join x y) z = join x (join y z) := by
    cases x <;> cases y <;> cases z <;> dsimp [join, coalesce]
    rename_i x y z
    simp

  theorem join_absorption : join x (meet x y) = x := by
    cases x <;> cases y <;> simp only [join, meet, map2_nil, coalesce, reduceCtorEq]
    rename_i x y
    by_cases H : ∀ (i : Fin n), x.val i ⊓ y.val i ≠ ⊥
    · simp [dif_pos H]
    · simp [dif_neg H]

  theorem join_bot : x.join bot = x := by
    cases x <;> simp [join]

  theorem join_top : x.join top = top := by
    cases x <;> simp [join, top, coalesce]

  theorem meet_commutative : meet x y = meet y x := by
    cases x <;> cases y <;> simp [meet, map2_nil, coalesce]
    rename_i x y
    simp [BoundedLattice.meet_commutative]
    split <;> rename_i H <;> [ rw [dif_pos] ; rw [dif_neg] ]
    <;> simp [H, BoundedLattice.meet_commutative]

  theorem meet_associative : meet (meet x y) z = meet x (meet y z) := by
    cases x <;> cases y <;> cases z <;> simp [meet, map2_nil, coalesce]
    rename_i x y z
    by_cases H : ∀ i, x.val i ⊓ y.val i ⊓ z.val i ≠ ⊥
    · rw [dif_pos]
      dsimp
      -- simp [dif_pos]
      rw [dif_pos, dif_pos]
      simp
      rw [dif_pos]

      all_goals intros i <;> specialize H i
      <;> have H' : (x.val i ⊓ y.val i) ⊓ z.val i ≠ ⊥ := by {
        rw [BoundedLattice.meet_associative]
        apply H
      }
      <;> next => first
        | apply BoundedLattice.meet_not_bot_left <;> assumption
        | apply BoundedLattice.meet_not_bot_right <;> assumption
        | assumption
    · have : ¬∀ i, (x.val i ⊓ y.val i) ⊓ z.val i ≠ ⊥ := by
        intros Hc
        apply H
        intros i
        rw [←BoundedLattice.meet_associative]
        apply Hc
      by_cases H' : ∀ (i : Fin n), ¬x.val i ⊓ y.val i = ⊥
      <;> [ rw [dif_pos H'] ; rw [dif_neg H'] ] <;> dsimp
      <;> (try rw [dif_neg this])
      <;> by_cases H'' : ∀ (i : Fin n), ¬y.val i ⊓ z.val i = ⊥
      <;> (first | rw [dif_pos H''] | rw [dif_neg H'']) <;> dsimp
      <;> rw [dif_neg H]

  theorem meet_absorption : meet x (join x y) = x := by
    cases x <;> cases y <;> simp [meet, join, map2_nil, coalesce]
    <;> try next x => simp [BoundedLattice.meet_idempotent, x.property]
    rename_i x y
    rw [dif_pos]
    simp [BoundedLattice.meet_absorption, x.property]

  theorem meet_top : x.meet top = x := by
    cases x <;> simp [meet, top, map2_nil, coalesce]
    rename_i x
    have H : ∀ i, x.val i ⊓ ⊤ ≠ ⊥ := by
      simp [BoundedLattice.meet_top, x.property]
    rw [dif_pos H]

  theorem meet_bot : x.meet bot = bot := by
    cases x <;> simp [meet, map2_nil]

  theorem non_trivial : (top : NonRelational α n) ≠ .bot := by
    simp [top]

  instance : BoundedLattice (NonRelational α n) where
    bot := bot
    top := top
    join := join
    meet := meet
    join_commutative := join_commutative
    join_associative := join_associative
    join_absorption := join_absorption
    join_bot := join_bot
    join_top := join_top
    meet_commutative := meet_commutative
    meet_associative := meet_associative
    meet_absorption := meet_absorption
    meet_top := meet_top
    meet_bot := meet_bot
    non_trivial := non_trivial

  def non_rel_subset : ∀ (x y : {env : Fin n → α // ∀ i, env i ≠ ⊥}),
    NonRelational.non_rel x ⊑ NonRelational.non_rel y
    ↔ ∀ i, x.val i ⊑ y.val i
  := by
    intros x y
    constructor <;> intros H
    · simp [BoundedLattice.is_subset, meet] at H
      unfold map2_nil at H
      unfold coalesce at H
      simp at H
      by_cases H' : ∀ (i : Fin n), ¬x.val i ⊓ y.val i = ⊥
      · rw [dif_pos H'] at H
        simp at H
        rw [H]
        simp
      · rw [dif_neg H'] at H
        cases H
    · simp [BoundedLattice.is_subset, meet]
      unfold map2_nil
      simp [coalesce]
      simp [BoundedLattice.is_subset] at H
      have H' : ∀ (i : Fin n), ¬x.val i ⊓ y.val i = ⊥ := by
        intros i
        specialize H i
        rw [←H]
        apply x.property
      rw [dif_pos H']
      cases x
      rename_i x Hx
      simp at *
      funext i
      apply H

  instance : Widen (NonRelational α n) where
    widen x y n := match x, y with
    | .non_rel x, .non_rel y => .non_rel
      <| .mk (fun i => ι.widen (x.val i) (y.val i) n)
      <| by
        intros i
        simp
        intros Hc
        apply x.property i
        apply BoundedLattice.antisymm
        · conv =>
            rhs
            rw [←Hc]
          apply WidenLawful.covering_left
        · apply BoundedLattice.bot_min
    | .bot, z | z, .bot => z

  instance : WidenLawful (NonRelational α n) where
    covering_left := by
      intros x y n
      cases x <;> cases y <;> simp [widen]
      <;> (try apply BoundedLattice.bot_min)
      <;> (try apply BoundedLattice.refl)
      rename_i x y
      rw [non_rel_subset]
      intros i
      simp
    covering_right := by
      intros x y n
      cases x <;> cases y <;> simp [widen]
      <;> (try apply BoundedLattice.bot_min)
      <;> (try apply BoundedLattice.refl)
      rename_i x y
      rw [non_rel_subset]
      intros i
      simp

  instance : Narrow (NonRelational α n) where
    narrow x y n := map2_nil x y fun x y =>
      fun i => ι.narrow (x i) (y i) n

  instance : NarrowLawful (NonRelational α n) where
    bounding_low := by
      intros x y n
      cases x <;> cases y <;> simp [Narrow.narrow, meet, map2_nil, coalesce]
      <;> (try apply BoundedLattice.bot_min)
      <;> (try apply BoundedLattice.refl)
      rename_i x y
      split
      case isFalse => apply BoundedLattice.bot_min
      case isTrue H =>
        have H' : ∀ i, Narrow.narrow (x.val i) (y.val i) n ≠ ⊥ := by
          intros i Hc
          apply H i
          apply BoundedLattice.min_bot_is_bot
          conv =>
            rhs
            rw [←Hc]
          simp
        rw [dif_pos H']
        rw [non_rel_subset]
        intros i
        simp
    bounding_high := by
      intros x y n
      cases x <;> cases y <;> simp [Narrow.narrow, meet, map2_nil, coalesce]
      <;> (try apply BoundedLattice.bot_min)
      <;> (try apply BoundedLattice.refl)
      rename_i x y
      split
      case isFalse => apply BoundedLattice.bot_min
      case isTrue H =>
        rw [non_rel_subset]
        intros i
        simp

  instance : DecidableEq (NonRelational α n) := fun x y => by
    cases x <;> cases y <;> simp <;>
    (try apply inferInstance) <;>
    clear x y z
    rename_i x y
    let ⟨x', Hx⟩ := x
    let ⟨y', Hy⟩ := y
    simp
    clear x y Hx Hy
    induction n
    case zero =>
      apply isTrue
      rw [funext_iff]
      intros i
      let ⟨i, Hi⟩ := i
      cases Hi
    case succ n IH =>
      rw [funext_iff]
      let restrict (f : Fin (n + 1) → α) (i : Fin n) : α := f i.succ
      cases (IH (restrict x') (restrict y')) <;> rename_i H
      · apply Decidable.isFalse
        intros Hc
        apply H
        rw [funext_iff]
        intros i
        cases i <;> rename_i n Hi
        simp [restrict]
        apply Hc
      · let zero : Fin (n + 1) := Fin.mk 0 (Nat.zero_lt_succ n)
        let HD := ι.eq_dec (x' zero) (y' zero)
        cases HD <;> rename_i H0
        · apply Decidable.isFalse
          intros Hc
          apply H0
          apply Hc
        · apply Decidable.isTrue
          apply Fin.cases
          · apply H0
          · have : ∀ {α β : Type} (f g : α → β), f = g → ∀x, f x = g x := by
              intros _ _ f g H x
              rw [H]
            intros i
            apply this (restrict x') (restrict y')
            assumption

  def get (i : Fin n) : α := match x with
  | .non_rel x => x.val i
  | .bot => ι.bot

  def update (i : Fin n) (a : α) : NonRelational α n :=
    x.map_nil fun x j => if i = j then a else x j

  def eval (x : NonRelational α n) : IExpr n → α
  | .nil => ι.nil
  | .top => ι.top
  | .var i => get x i
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

  def assign (i : Fin n) (e : IExpr n) :
    NonRelational α n
  :=
    update x i (eval x e)

  def backward_eval (x : NonRelational α n) (e : IExpr n) (r : α) :
    NonRelational α n
  :=
    let _ : DecidableEq α := ι.eq_dec -- help class inference
    match e with
    | .nil => if ι.is_bot (ι.meet r ι.nil)
      then BoundedLattice.bot
      else x
    | .top => x
    | .var i => update x i (ι.meet (get x i) r)
    | .rand a b => if ι.is_bot (ι.meet r (ι.rand a b))
      then BoundedLattice.bot
      else x
    | .const n => if ι.is_bot (ι.meet r (ι.from_const n))
      then BoundedLattice.bot
      else x
    | .neg e =>
      let i := eval x e
      let r := ι.backward_neg i r
      backward_eval x e r
    | .binop e₁ op e₂ =>
      let i₁ := eval x e₁
      let i₂ := eval x e₂
      let (r₁, r₂) := match op with
      | .iadd => ι.backward_add i₁ i₂ r
      | .isub => ι.backward_sub i₁ i₂ r
      | .imul => ι.backward_mul i₁ i₂ r
      | .idiv => ι.backward_div i₁ i₂ r
      backward_eval x e₁ r₁ ⊓ backward_eval x e₂ r₂

  def guard (x : NonRelational α n) (b : BExpr n) :
    NonRelational α n
  := match b with
  | .random | .const true => x
  | .const false => BoundedLattice.bot
  | .compare e₁ op e₂ =>
    let i₁ := eval x e₁
    let i₂ := eval x e₂
    let (r₁, r₂) := ι.compare op i₁ i₂
    backward_eval x e₁ r₁ ⊓ backward_eval x e₂ r₂
  | .or b₁ b₂ => guard x b₁ ⊔ guard x b₂
  | .and b₁ b₂ => guard x b₁ ⊓ guard x b₂

  instance : Domain (NonRelational α n) where
    new := coalesce fun _ => ValueDomain.new
    nb_var := n
    eq_dec := inferInstance
    assign := assign
    guard := guard
    -- TODO: pourquoi ça n'infère pas ??
    covering_left := WidenLawful.covering_left
    covering_right := WidenLawful.covering_right

    bounding_low := NarrowLawful.bounding_low
    bounding_high := NarrowLawful.bounding_high
end NonRelational
