import Lustrean.Domain
import Lustrean.Facts

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
    apply Int.min_assoc

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

  @[simp]
  theorem max_refl : ∀ (n : IntLow),
    max n n = n :=
  by
    intro n
    cases n <;> simp [max]
    apply Int.max_eq_left
    apply Int.le_refl

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
    apply Int.max_assoc

  theorem min_max_absorb : ∀ (l₁ l₂ : IntLow),
    min l₁ (max l₁ l₂) = l₁ :=
  by
    intro l₁ l₂
    cases l₁ <;> cases l₂ <;> simp [min, max]
    · apply Int.min_max_absorb
    · apply Int.min_eq_left
      apply Int.le_refl

  theorem max_min_absorb : ∀ (l₁ l₂ : IntLow),
    max l₁ (min l₁ l₂) = l₁ :=
  by
    intro l₁ l₂
    cases l₁ <;> cases l₂ <;> simp [min, max]
    apply Int.max_min_absorb

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
    apply Int.max_assoc

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

  @[simp]
  theorem min_refl : ∀ (n : IntHigh),
    min n n = n :=
  by
    intro n
    cases n <;> simp [min]
    apply Int.min_eq_left
    apply Int.le_refl

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
    apply Int.min_assoc

  theorem max_min_absorb : ∀ (h₁ h₂ : IntHigh),
    max h₁ (min h₁ h₂) = h₁ :=
  by
    intro h₁ h₂
    cases h₁ <;> cases h₂ <;> simp [min, max]
    apply Int.max_min_absorb
    apply Int.max_eq_left
    apply Int.le_refl

  theorem min_max_absorb : ∀ (h₁ h₂ : IntHigh),
    min h₁ (max h₁ h₂) = h₁ :=
  by
    intro h₁ h₂
    cases h₁ <;> cases h₂ <;> simp [min, max]
    apply Int.min_max_absorb

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
end HLe

namespace IntLow
  def sub_l_h (l : IntLow) (h : IntHigh) : IntLow :=
    match l, h with
    | .minf, _ | _, .pinf => .minf
    | .int n, .int m => .int (n - m)
end IntLow

namespace IntHigh
  def sub_h_l (h : IntHigh) (l : IntLow) : IntHigh :=
    match h, l with
    | .pinf, _ | _, .minf => .pinf
    | .int n, .int m => .int (n - m)
end IntHigh

namespace HLe
  theorem sub_monotone : ∀ (l₁ l₂ : IntLow) (h₁ h₂ : IntHigh),
    l₁ ≤∘ h₁ → l₂ ≤∘ h₂ → IntLow.sub_l_h l₁ h₂ ≤∘ IntHigh.sub_h_l h₁ l₂ :=
  by
    intro l₁ l₂ h₁ h₂ hyp₁ hyp₂
    cases l₁ <;> cases l₂ <;> cases h₁ <;> cases h₂ <;> try constructor
    rename_i a b c d
    cases hyp₁ <;> cases hyp₂ <;>
    apply Int.sub_le_sub <;> assumption

  theorem min_max_monotone : ∀ (l₁ l₂ : IntLow) (h₁ h₂ : IntHigh),
    l₁ ≤∘ h₁ → l₂ ≤∘ h₂ → min l₁ l₂ ≤∘ max h₁ h₂ :=
  by
    intro l₁ l₂ h₁ h₂ hyp₁ hyp₂
    cases l₁ <;> cases l₂ <;> cases h₁ <;> cases h₂ <;>
    try constructor
    rename_i a b c d
    skip
    apply Int.le_trans
    · apply Int.min_le_left
    · apply Int.le_trans
      · cases hyp₁
        assumption
      · apply Int.le_max_left

  theorem min_min_max_max : ∀ (l₁ l₂ l₃ : IntLow) (h₁ h₂ h₃ : IntHigh),
    max (max l₁ l₂) l₃ ≤∘ min (min h₁ h₂) h₃ →
    (max l₁ l₂ ≤∘ min h₁ h₂) ∧ (max l₂ l₃ ≤∘ min h₂ h₃) :=
  by
    intro l₁ l₂ l₃ h₁ h₂ h₃ h
    apply And.intro <;>
    cases l₁ <;> cases l₂ <;> cases l₃ <;>
    cases h₁ <;> cases h₂ <;> cases h₃ <;>
    cases h <;> simp [min, max, IntLow.max, IntHigh.min] <;>
    (try assumption) <;> omega
end HLe

namespace IntLow
  def mul_l_h (l : IntLow) (h : IntHigh) : Option IntLow :=
    match l, h with
    | .minf, .pinf => some .minf
    | .minf, .int n => match compare n 0 with
      | .lt => none
      | .eq => some (.int 0)
      | .gt => some .minf
    | .int n, .pinf => match compare n 0 with
      | .lt => some .minf
      | .eq => some (.int 0)
      | .gt => none
    | .int n, .int m => some (.int (n * m))

  def mul_l_l (l₁ l₂ : IntLow) : Option IntLow :=
    match l₁, l₂ with
    | .minf, .minf => none
    | .int n, .int m => some (.int (n * m))
    | .minf, .int n
    | .int n, .minf => match compare n 0 with
      | .lt => none
      | .eq => some (.int 0)
      | .gt => some .minf

  def mul_h_h (h₁ h₂ : IntHigh) : Option IntLow :=
    match h₁, h₂ with
    | .pinf, .pinf => none
    | .int n, .int m => some (.int (n * m))
    | .pinf, .int n
    | .int n, .pinf => match compare n 0 with
      | .lt => some .minf
      | .eq => some (.int 0)
      | .gt => none
end IntLow

namespace IntHigh
  def mul_h_l (h : IntHigh) (l : IntLow) : Option IntHigh :=
    match h, l with
    | .pinf, .minf => some .pinf
    | .pinf, .int n => match compare n 0 with
      | .lt => none
      | .eq => some (.int 0)
      | .gt => some .pinf
    | .int n, .minf => match compare n 0 with
      | .lt => some .pinf
      | .eq => some (.int 0)
      | .gt => none
    | .int n, .int m => some (.int (n * m))

  def mul_h_h (h₁ h₂ : IntHigh) : Option IntHigh :=
    match h₁, h₂ with
    | .pinf, .pinf => some .pinf
    | .int n, .int m => some (.int (n * m))
    | .pinf, .int n
    | .int n, .pinf => match compare n 0 with
      | .lt => none
      | .eq => some (.int 0)
      | .gt => some .pinf

  def mul_l_l (l₁ l₂ : IntLow) : Option IntHigh :=
    match l₁, l₂ with
    | .minf, .minf => some .pinf
    | .int n, .int m => some (.int (n * m))
    | .minf, .int n
    | .int n, .minf => match compare n 0 with
      | .lt => some .pinf
      | .eq => some (.int 0)
      | .gt => none
end IntHigh

-- Parameterized by the list of constants
-- in the source program, in order to do
-- a better widening
inductive Interval (constants : List Int) where
  | empty : Interval constants
  | interval (low : IntLow) (high : IntHigh) : low ≤∘ high → Interval constants

namespace Interval
  variable {constants : List Int}
  variable (x y z : Interval constants)

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
    .interval (IntLow.sub_l_h l₁ h₂) (IntHigh.sub_h_l h₁ l₂)
      <| by apply HLe.sub_monotone <;> assumption

  instance : Sub (Interval constants) where
    sub := sub

  def bot : Interval constants := .empty

  def top : Interval constants := .interval .minf .pinf <| by constructor

  def join : Interval constants := match x, y with
  | .empty, z | z, .empty => z
  | .interval l₁ h₁ o₁, .interval l₂ h₂ o₂ =>
    .interval (min l₁ l₂) (max h₁ h₂) <| by apply HLe.min_max_monotone <;> assumption

  def meet : Interval constants := match x, y with
  | .empty, _ | _, .empty => .empty
  | .interval l₁ h₁ _, .interval l₂ h₂ _ =>
    if h : max l₁ l₂ ≤∘ min h₁ h₂
    then .interval (max l₁ l₂) (min h₁ h₂) h
    else .empty

  theorem join_commutative : join x y = join y x :=
  by
    cases x <;> cases y <;> simp [join]
    apply And.intro
    · apply IntLow.min_comm
    · apply IntHigh.max_comm

  theorem join_associative : join (join x y) z = join x (join y z) :=
  by
    cases x <;> cases y <;> cases z <;> dsimp [join]
    simp [min, max, IntLow.min_assoc, IntHigh.max_assoc]

  theorem join_absorption : join x (meet x y) = x :=
  by
    cases x <;> cases y <;> dsimp [join, meet]
    rename_i l₁ h₁ hyp₁ l₂ h₂ hyp₂
    by_cases h : max l₁ l₂ ≤∘ min h₁ h₂
    · rw [dif_pos h]
      dsimp
      simp [min, max, IntLow.min_max_absorb, IntHigh.max_min_absorb]
    · rw [dif_neg h]

  theorem join_bot : join x bot = x :=
  by
    cases x <;> dsimp [bot, join]

  theorem join_top : join x top = top :=
  by
    cases x <;>
    simp [join, top, min, max, IntLow.min_minf, IntHigh.max_pinf]

  theorem meet_commutative : meet x y = meet y x :=
  by
    cases x <;> cases y <;> simp [meet]
    split <;> split <;> try dsimp
    · simp [min, max, IntLow.max_comm, IntHigh.min_comm]
    all_goals try next hyp₁ hyp₂ =>
      exfalso
      simp [min, max] at hyp₁
      simp [min, max] at hyp₂
      rw [IntLow.max_comm, IntHigh.min_comm] at hyp₁
      solve | exact (hyp₁ hyp₂) | exact (hyp₂ hyp₁)

  theorem meet_associative :
    meet (meet x y) z = meet x (meet y z) :=
  by
    cases x <;> cases y <;> cases z <;> simp [meet]
    · rename_i l₁ h₁ hyp₁ l₂ h₂ hyp₂
      by_cases h : max l₁ l₂ ≤∘ min h₁ h₂
      · rw [dif_pos h]
      · rw [dif_neg h]
    · rename_i l₁ h₁ hyp₁ l₂ h₂ hyp₂ l₃ h₃ hyp₃
      by_cases h : max l₁ l₂ ≤∘ min h₁ h₂
      · rw [dif_pos h] ; dsimp
        by_cases h' : max l₂ l₃ ≤∘ min h₂ h₃
        · rw [dif_pos h'] ; dsimp
          simp [min, max, IntLow.max_assoc, IntHigh.min_assoc]
        · rw [dif_neg h'] ; rw [dif_neg]
          intro H
          apply h'
          apply And.right
          apply HLe.min_min_max_max
          apply H
      · rw [dif_neg h] ; dsimp
        by_cases h' : max l₂ l₃ ≤∘ min h₂ h₃
        · rw [dif_pos h'] ; dsimp; rw [dif_neg]
          intro H
          apply h
          apply And.left
          apply HLe.min_min_max_max
          simp [min, max]
          rw [IntLow.max_assoc, IntHigh.min_assoc]
          apply H
        · rw [dif_neg h']

  theorem meet_absorption : meet x (join x y) = x :=
  by
    cases x <;> cases y <;> dsimp [join, meet]
    · rename_i l₁ h₁ hyp₁
      rw [dif_pos] <;> simp [max, min, IntLow.max_refl, IntHigh.min_refl]
      assumption
    · rename_i l₁ h₁ hyp₁ l₂ h₂ hyp₂
      simp [min, max, IntLow.max_min_absorb, IntHigh.min_max_absorb]
      rw [dif_pos hyp₁]

  theorem meet_bot : meet x bot = bot :=
  by
    cases x <;> dsimp [meet, bot]

  theorem meet_top : meet x top = x :=
  by
    cases x <;> simp [meet, top, max, min]
    rename_i h
    rw [dif_pos h]

  instance : BoundedLattice (Interval constants) where
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
    meet_bot := meet_bot
    meet_top := meet_top

  def toString := match x with
  | .empty => "∅"
  | .interval l h _ => s!"[{l}; {h}]"

  instance : ToString (Interval constants) where
    toString := toString
end Interval

def get_min_mul_bound_opt (l₁ l₂ : IntLow) (h₁ h₂ : IntHigh) : Option IntLow :=
  List.foldl (
    fun x y => match x, y with
    | none, none => none
    | none, some z | some z, none => some z
    | some x, some y => IntLow.min x y
  ) none [
    l₁.mul_l_h h₂, l₁.mul_l_l l₂, l₂.mul_l_h h₁, IntLow.mul_h_h h₁ h₂
  ]

theorem get_min_mul_bound_opt_not_none : ∀ (l₁ l₂ : IntLow) (h₁ h₂ : IntHigh)
  (o₁ : l₁ ≤∘ h₁) (o₂ : l₂ ≤∘ h₂),
  get_min_mul_bound_opt l₁ l₂ h₁ h₂ ≠ none :=
by
  intros l₁ l₂ h₁ h₂ o₁ o₂ hcontra
  cases l₁ <;> cases l₂ <;> cases h₁ <;> cases h₂ <;>
  dsimp [get_min_mul_bound_opt, IntLow.mul_l_h, IntLow.mul_l_l, IntLow.mul_h_h] at hcontra <;>
  sorry

def get_min_mul_bound (l₁ l₂ : IntLow) (h₁ h₂ : IntHigh)
  (o₁ : l₁ ≤∘ h₁) (o₂ : l₂ ≤∘ h₂) : IntLow :=
by
  cases h : get_min_mul_bound_opt l₁ l₂ h₁ h₂
  · exfalso
    apply get_min_mul_bound_opt_not_none l₁ l₂ <;> try assumption
  · rename_i val
    exact val

def get_max_mul_bound_opt (l₁ l₂ : IntLow) (h₁ h₂ : IntHigh) : Option IntHigh :=
  List.foldl (
    fun x y => match x, y with
    | none, none => none
    | none, some z | some z, none => some z
    | some x, some y => IntHigh.max x y
  ) none [
    h₁.mul_h_l l₂, h₁.mul_h_h h₂, h₂.mul_h_l l₁, IntHigh.mul_l_l l₁ l₂
  ]

theorem get_max_mul_bound_opt_not_none : ∀ (l₁ l₂ : IntLow) (h₁ h₂ : IntHigh)
  (o₁ : l₁ ≤∘ h₁) (o₂ : l₂ ≤∘ h₂),
  get_max_mul_bound_opt l₁ l₂ h₁ h₂ ≠ none :=
by sorry

def get_max_mul_bound (l₁ l₂ : IntLow) (h₁ h₂ : IntHigh)
  (o₁ : l₁ ≤∘ h₁) (o₂ : l₂ ≤∘ h₂) : IntHigh :=
by
  cases h : get_max_mul_bound_opt l₁ l₂ h₁ h₂
  · exfalso
    apply get_max_mul_bound_opt_not_none l₁ l₂ <;> try assumption
  · rename_i val
    exact val

instance {constants : List Int} : Mul (Interval constants) where
  mul x y := .map_empty x y <| fun l₁ l₂ h₁ h₂ o₁ o₂ =>
    let l := get_min_mul_bound l₁ l₂ h₁ h₂ o₁ o₂
    let h := get_max_mul_bound l₁ l₂ h₁ h₂ o₁ o₂
    .interval l h <| by sorry

instance {constants : List Int}
  [ι : BoundedLattice (Interval constants)] :
  DecidableRel (fun x y => x = ι.meet x y) :=
by
  sorry

instance {constants : List Int} : ValueDomain (Interval constants) where
  new := .interval (.int 0) (.int 0) <| by simp
  from_const x := .interval (.int x) (.int x) <| by simp
  rand x y := if h : x ≤ y
    then .interval (.int x) (.int y) <| by constructor; assumption
    else .empty
  widen n x y := if n <= 100
    then
      x.join y
    else
      sorry
  narrow _ _ _ := sorry
  subset_dec := sorry
  is_bot_dec := sorry
