import Lustrean.Domain

-- int or -∞
structure IntLow where n : Option Int

-- int or +∞
structure IntHigh where n : Option Int

def ordered (low : IntLow) (high : IntHigh) : Prop :=
  match low, high with
  | ⟨ none ⟩, _ | _, ⟨ none ⟩  => True
  | ⟨ some n ⟩, ⟨ some m ⟩ => n <= m

-- Parameterized by the list of constants
-- in the source program, in order to do
-- a better widening
inductive Interval (constants : List Int) where
| empty : Interval constants
| interval (low : IntLow) (high : IntHigh) : ordered low high -> Interval constants

def map_empty {constants : List Int} (x y : Interval constants)
  (f : forall (low1 : IntLow) (low2 : IntLow)
    (high1 : IntHigh) (high2 : IntHigh),
    ordered low1 high1 -> ordered low2 high2 ->
    Interval constants)
  : Interval constants :=
  match x, y with
  | .empty, _ | _, .empty => .empty
  | .interval l1 h1 o1, .interval l2 h2 o2 => f l1 l2 h1 h2 o1 o2

instance (constants : List Int) : BoundedLattice (Interval constants) where
  bot := Interval.empty
  top := Interval.interval (IntLow.mk none) (IntHigh.mk none) True.intro

instance {constants : List Int} : Add (Interval constants)
where
  add x y := map_empty x y (
    fun l1 l2 h1 h2 o1 o2 =>
    let l := match l1, l2 with
    | ⟨ none ⟩, _ | _, ⟨ none ⟩ => ⟨ none ⟩
    | ⟨ some a ⟩ , ⟨ some b ⟩  => ⟨ some (a + b) ⟩
    let h := match h1, h2 with
    | ⟨ none ⟩, _ | _, ⟨ none ⟩ => ⟨ none ⟩
    | ⟨ some a ⟩ , ⟨ some b ⟩  => ⟨ some (a + b) ⟩
    .interval l h _
  )

instance {constants : List Int} : Sub (Interval constants)
where
  sub x y := map_empty x y (
    fun l1 l2 h1 h2 o1 o2 =>
    let l := match l1, h2 with
    | ⟨ none ⟩, _ | _, ⟨ none ⟩ => ⟨ none ⟩
    | ⟨ some a ⟩ , ⟨ some b ⟩  => ⟨ some (a - b) ⟩
    let h := match h1, l2 with
    | ⟨ none ⟩, _ | _, ⟨ none ⟩ => ⟨ none ⟩
    | ⟨ some a ⟩ , ⟨ some b ⟩  => ⟨ some (a - b) ⟩
    .interval l h _
  )
