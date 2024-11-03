import Lustrean.Domain

-- int or -∞
inductive IntLow where
  | int (n : Int)
  | minf

namespace IntLow
  inductive Le : IntLow → IntLow → Prop where
    | minf m : Le .minf m
    | leq n m : n ≤ m → Le (.int n) (.int m)

  instance : LE IntLow where
    le := Le

  def add (n m : IntLow) : IntLow :=
    match n, m with
    | .minf, _ | _, .minf => .minf
    | .int n, .int m => .int (n + m)

  instance : Add IntLow where
    add := add

  @[simp]
  theorem add_minf_m : ∀ m : IntLow, .minf + m = .minf := by
    intros m
    cases m <;> rfl

  @[simp]
  theorem add_n_minf : ∀ n : IntLow, n + .minf = .minf := by
    intros n
    cases n <;> rfl

  @[simp]
  theorem add_n_m : ∀ n m, .int n + .int m = IntLow.int (n + m) := by
    intros
    rfl
end IntLow

-- int or +∞
inductive IntHigh where
  | int (n : Int)
  | pinf

namespace IntHigh
  inductive Le : IntHigh → IntHigh → Prop where
    | pinf_ge n : Le n pinf
    | leq n m : n ≤ m → Le (.int n) (.int m)

  instance : LE IntHigh where
    le := Le

  def add (n m : IntHigh) : IntHigh :=
    match n, m with
    | .pinf, _ | _, .pinf => .pinf
    | .int n, .int m => .int (n + m)

  instance : Add IntHigh where
    add := add

  @[simp]
  theorem add_pinf_m : ∀ m, .pinf + m = IntHigh.pinf := by
    intros m
    cases m <;> rfl

  @[simp]
  theorem add_n_pinf : ∀ n, n + .pinf = IntHigh.pinf := by
    intros n
    cases n <;> rfl

  @[simp]
  theorem add_n_m : ∀ n m, .int n + .int m = IntHigh.int (n + m) := by
    intros
    rfl
end IntHigh

inductive HLe : IntLow → IntHigh → Prop where
  | minf m : HLe .minf m
  | pinf n : HLe n .pinf
  | int_ord n m : n ≤ m → HLe (.int n) (.int m)

namespace HLe
  infix:30 " ≤∘ " => HLe

  @[simp]
  theorem hle_int : ∀ n m, .int n ≤∘ .int m ↔ n ≤ m := by
    intros n m
    constructor <;>
    intro leq <;>
    (first | cases leq | constructor) <;>
    assumption

  @[simp]
  theorem hle_minf : ∀ m, .minf ≤∘ m := by
    intro
    constructor

  @[simp]
  theorem hle_pinf : ∀ n, n ≤∘ .pinf := by
    intro
    constructor

  instance (low : IntLow) (high : IntHigh) : Decidable (low ≤∘ high) := by
    cases low <;>
    cases high <;>
    simp <;>
    apply inferInstance

  theorem add_monotone : ∀ n₁ n₂ m₁ m₂, n₁ ≤∘ m₁ → n₂ ≤∘ m₂ → n₁ + n₂ ≤∘ m₁ + m₂ := by
    intros n₁ n₂ m₁ m₂ n₁_leq_m₁ n₂_leq_m₂
    cases n₁
    case minf => simp
    cases n₂
    case minf => simp
    cases m₁
    case pinf => simp
    cases m₂
    case pinf => simp
    cases n₁_leq_m₁
    cases n₂_leq_m₂
    simp
    omega

  def sub_l_h (l : IntLow) (h : IntHigh) : IntLow :=
    match l, h with
    | .minf, _ | _, .pinf => .minf
    | .int n, .int m => .int (n - m)

  def sub_h_l (h : IntHigh) (l : IntLow) : IntHigh :=
    match h, l with
    | .pinf, _ | _, .minf => .pinf
    | .int n, .int m => .int (n - m)

  theorem sub_monotone : ∀ (l₁ l₂ : IntLow) (h₁ h₂ : IntHigh),
    l₁ ≤∘ h₁ → l₂ ≤∘ h₂ → sub_l_h l₁ h₂ ≤∘ sub_h_l h₁ l₂ := by
  intro l₁ l₂ h₁ h₂ hyp₁ hyp₂
  cases l₁ <;> cases l₂ <;> cases h₁ <;> cases h₂ <;> try constructor
  next a b c d =>
    cases hyp₁ <;> cases hyp₂ <;>
    apply Int.sub_le_sub <;> assumption
end HLe

-- Parameterized by the list of constants
-- in the source program, in order to do
-- a better widening
inductive Interval (constants : List Int) where
  | empty : Interval constants
  | interval (low : IntLow) (high : IntHigh) : low ≤∘ high → Interval constants

namespace Interval
  variable {constants : List Int}
  variable (x y : Interval constants)

  def map_empty (f : (low₁ low₂ : IntLow) → (high₁ high₂ : IntHigh) →
                     low₁ ≤∘ high₁ → low₂ ≤∘ high₂ →
                     Interval constants)
                : Interval constants :=
    match x, y with
    | .empty, _ | _, .empty => .empty
    | .interval l₁ h₁ o₁, .interval l₂ h₂ o₂ => f l₁ l₂ h₁ h₂ o₁ o₂

  def add : Interval constants :=
    map_empty x y <| fun l₁ l₂ h₁ h₂ o₁ o₂ =>
      .interval (l₁ + l₂) (h₁ + h₂) <| by apply HLe.add_monotone <;> assumption

  instance : Add (Interval constants) where
    add := add

  def sub : Interval constants :=
  Interval.map_empty x y <| fun l₁ l₂ h₁ h₂ le₁ le₂ =>
    .interval (HLe.sub_l_h l₁ h₂) (HLe.sub_h_l h₁ l₂)
      <| by apply HLe.sub_monotone <;> assumption

  instance : Sub (Interval constants) where
    sub := sub
end Interval
