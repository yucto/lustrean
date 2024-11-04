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

  def min (n m : IntLow) : IntLow :=
    match n, m with
    | .minf, _ | _, .minf => .minf
    | .int n, .int m => .int (Min.min n m)

  instance : Min IntLow where
    min := min

  @[simp]
  theorem min_minf : ∀ (n : IntLow),
    min n .minf = .minf :=
  by
    intro n; cases n <;> simp [min]

  @[simp]
  theorem minf_min : ∀ (n : IntLow),
    min .minf n = .minf :=
  by
    intro n; cases n <;> simp [min]

  theorem min_comm : ∀ (n m : IntLow),
    min n m = min m n :=
  by
    intro n m
    cases n <;> cases m <;>
    simp [min, Int.min_comm]

  theorem min_assoc : ∀ (n m o : IntLow),
    min (min n m) o = min n (min m o) :=
  by
    intro n m o
    cases n <;> cases m <;> cases o <;> simp [min]
    sorry

  def max (n m : IntLow) : IntLow :=
    match n, m with
    | .int n, .int m => .int (Max.max n m)
    | .int n, .minf | .minf, .int n => .int n
    | .minf, .minf => .minf

  instance : Max IntLow where
    max := max

  @[simp]
  theorem max_minf : ∀ (n : IntLow),
    max n .minf = n :=
  by
    intro n
    cases n <;> simp [max]

  @[simp]
  theorem minf_max : ∀ (n : IntLow),
    max .minf n = n :=
  by
    intro n
    cases n <;> simp [max]

  theorem max_comm : ∀ (n m : IntLow),
    max n m = max m n :=
  by
    intro n m
    cases n <;> cases m <;>
    simp [max, Int.max_comm]

  theorem max_assoc : ∀ (n m o : IntLow),
    max (max n m) o = max n (max m o) :=
  by
    intro n m o
    cases n <;> cases m <;> cases o <;> simp [max]
    sorry

  instance : ToString IntLow where
    toString n := match n with
    | .minf => "-∞"
    | .int n => toString n
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

  def max (n m : IntHigh) : IntHigh :=
    match n, m with
    | .pinf, _ | _, .pinf => .pinf
    | .int n, .int m => .int (Max.max n m)

  instance : Max IntHigh where
    max := max

  @[simp]
  theorem max_pinf : ∀ (n : IntHigh),
    max n .pinf = .pinf :=
  by
    intro n; cases n <;> simp [max]

  @[simp]
  theorem pinf_max : ∀ (n : IntHigh),
    max .pinf n = .pinf :=
  by
    intro n; cases n <;> simp [max]


  theorem max_comm : ∀ (n m : IntHigh),
    max n m = max m n :=
  by
    intro n m
    cases n <;> cases m <;>
    simp [max, Int.max_comm]

  theorem max_assoc : ∀ (n m o : IntHigh),
    max (max n m) o = max n (max m o) :=
  by
    intro n m o
    cases n <;> cases m <;> cases o <;> simp [max]
    sorry

  def min (n m : IntHigh) : IntHigh :=
    match n, m with
    | .int n, .int m => .int (Min.min n m)
    | .int n, .pinf | .pinf, .int n => .int n
    | .pinf, .pinf => .pinf

  instance : Min IntHigh where
    min := min

  @[simp]
  theorem min_pinf : ∀ (n : IntHigh),
    min n .pinf = n :=
  by
    intro n
    cases n <;> simp [min]

  @[simp]
  theorem pinf_min : ∀ (n : IntHigh),
    min .pinf n = n :=
  by
    intro n
    cases n <;> simp [min]

  theorem min_comm : ∀ (n m : IntHigh),
    min n m = min m n :=
  by
    intro n m
    cases n <;> cases m <;>
    simp [min, Int.min_comm]

  theorem min_assoc : ∀ (n m o : IntHigh),
    min (min n m) o = min n (min m o) :=
  by
    intro n m o
    cases n <;> cases m <;> cases o <;> simp [min]
    sorry

  instance : ToString IntHigh where
    toString n := match n with
    | .pinf => "+∞"
    | .int n => toString n
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
    l₁ ≤∘ h₁ → l₂ ≤∘ h₂ → sub_l_h l₁ h₂ ≤∘ sub_h_l h₁ l₂ :=
  by
    intro l₁ l₂ h₁ h₂ hyp₁ hyp₂
    cases l₁ <;> cases l₂ <;> cases h₁ <;> cases h₂ <;> try constructor
    next a b c d =>
      cases hyp₁ <;> cases hyp₂ <;>
      apply Int.sub_le_sub <;> assumption

  theorem min_max_monotone : ∀ (l₁ l₂ : IntLow) (h₁ h₂ : IntHigh),
    l₁ ≤∘ h₁ → l₂ ≤∘ h₂ → min l₁ l₂ ≤∘ max h₁ h₂ :=
  by
    intro l₁ l₂ h₁ h₂ hyp₁ hyp₂
    cases l₁ <;> cases l₂ <;> cases h₁ <;> cases h₂ <;>
    try constructor
    next a b c d =>
      skip
      apply Int.le_trans
      · apply Int.min_le_left
      · apply Int.le_trans
        · cases hyp₁
          assumption
        · apply Int.le_max_left
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

instance {constants : List Int} : BoundedLattice (Interval constants) where
  bot := .empty
  top := .interval .minf .pinf <| by constructor
  join x y := match x, y with
  | .empty, z | z, .empty => z
  | .interval l₁ h₁ o₁, .interval l₂ h₂ o₂ =>
    .interval (min l₁ l₂) (max h₁ h₂) <| by apply HLe.min_max_monotone <;> assumption
  meet x y := match x, y with
  | .empty, _ | _, .empty => .empty
  | .interval l₁ h₁ _, .interval l₂ h₂ _ =>
    if h : max l₁ l₂ ≤∘ min h₁ h₂
    then .interval (max l₁ l₂) (min h₁ h₂) h
    else .empty
  join_commutative := by
    intro x y
    cases x <;> cases y <;> simp
    apply And.intro
    · apply IntLow.min_comm
    · apply IntHigh.max_comm
  join_associative := by
    intro x y z
    cases x <;> cases y <;> cases z <;> dsimp
    simp [min, max, IntLow.min_assoc, IntHigh.max_assoc]
  join_absorption := by
    intro x y
    cases x <;> cases y <;> dsimp
    next l₁ h₁ hyp₁ l₂ h₂ hyp₂ =>
      by_cases h : max l₁ l₂ ≤∘ min h₁ h₂
      · rw [dif_pos h]
        dsimp
        sorry
      · rw [dif_neg h]
  join_top := by
    intro x
    cases x <;> dsimp
    simp [min, max, IntLow.min_minf, IntHigh.max_pinf]
  join_bot := by
    intro x
    cases x <;> dsimp
  meet_commutative := by
    intro x y
    cases x <;> cases y <;> simp
    split <;> split <;> try dsimp
    · simp [min, max, IntLow.max_comm, IntHigh.min_comm]
    all_goals try next hyp₁ hyp₂ =>
      exfalso
      simp [min, max] at hyp₁
      simp [min, max] at hyp₂
      rw [IntLow.max_comm, IntHigh.min_comm] at hyp₁
      try exact (hyp₁ hyp₂)
      try exact (hyp₂ hyp₁)
  meet_associative := by
    intro x y z
    cases x <;> cases y <;> cases z <;> simp
    · next l₁ h₁ hyp₁ l₂ h₂ hyp₂ =>
      by_cases h : max l₁ l₂ ≤∘ min h₁ h₂
      · rw [dif_pos h]
      · rw [dif_neg h]
    · next l₁ h₁ hyp₁ l₂ h₂ hyp₂ l₃ h₃ hyp₃ =>
      by_cases h : max l₁ l₂ ≤∘ min h₁ h₂
      · rw [dif_pos h] ; dsimp
        by_cases h' : max l₂ l₃ ≤∘ min h₂ h₃
        · rw [dif_pos h'] ; dsimp
          simp [min, max, IntLow.max_assoc, IntHigh.min_assoc]
        · rw [dif_neg h'] ; rw [dif_neg]
          simp [min, max]
          sorry
      · rw [dif_neg h] ; dsimp
        by_cases h' : max l₂ l₃ ≤∘ min h₂ h₃
        · rw [dif_pos h'] ; dsimp; rw [dif_neg]
          simp [min, max]
          sorry
        · rw [dif_neg h']
  meet_absorption := by sorry
  meet_top := by
    intro x
    cases x <;> dsimp
    next h =>
      simp [min, max]
      rw [dif_pos h]
  meet_bot := by
    intro x
    cases x <;> dsimp

theorem a : ∀ (l1 l2 l3 : IntLow) (h1 h2 h3 : IntHigh),
  max (max l1 l2) l3 ≤∘ min (min h1 h2) h3 ->
  (max l1 l2 ≤∘ min h1 h2) /\ (max l2 l3 ≤∘ min h2 h3) :=
by
  intro l1 l2 l3 h1 h2 h3 hyp
  constructor
  · try apply trans
    sorry
  · sorry

instance {constants : List Int} : ToString (Interval constants) where
  toString x := match x with
  | .empty => "∅"
  | .interval l h _ => s!"[{l}; {h}]"

instance {constants : List Int} : Mul (Interval constants) where
  mul x y := match x, y with
  | _, _ => sorry

instance {constants : List Int} : ValueDomain (Interval constants) where
  new := .interval (.int 0) (.int 0) <| by simp
  from_const x := .interval (.int x) (.int x) <| by simp
  rand x y := if h : x ≤ y
    then .interval (.int x) (.int y) <| by constructor; assumption
    else .empty
  widen _ _ _ := sorry
  narrow _ _ _ := sorry
  is_bottom x := match x with
  | .empty => true
  | _ => false
  is_bottom_correct := by
    intro x
    cases x <;> simp [BoundedLattice.bot]
  subset x y := sorry
  subset_correct x y := sorry
