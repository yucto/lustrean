class BoundedLattice (α : Type) where
  bot : α
  top : α
  join : α → α → α
  meet : α → α → α
  join_commutative : ∀ (x y : α), join x y = join y x
  join_associative : ∀ (x y z : α), join (join x y) z = join x (join y z)
  join_absorption : ∀ (x y : α), join x (meet x y) = x
  join_bot : ∀ (x : α), join x bot = x
  join_top : ∀ (x : α), join x top = top
  meet_commutative : ∀ (x y : α), meet x y = meet y x
  meet_associative : ∀ (x y z : α), meet (meet x y) z = meet x (meet y z)
  meet_absorption : ∀ (x y : α), meet x (join x y) = x
  meet_top : ∀ (x : α), meet x top = x
  meet_bot : ∀ (x : α), meet x bot = bot

class Domain (α : Type)
extends Add α, Mul α, Sub α, BoundedLattice α, ToString α
where
  new : α
  -- Nat : number of iterations
  widen : Nat → α → α → α
  -- Nat : number of iterations
  narrow : Nat → α → α → α
  subset_dec : DecidableRel (fun x y => x = meet x y)
  is_bot_dec : DecidablePred (· = bot)
  -- TODO: guard, assign

instance (α : Type) [ι : Domain α] :
  DecidablePred (· = ι.bot) :=
  Domain.is_bot_dec

instance (α : Type) [ι : Domain α] :
  DecidableRel (fun x y => x = ι.meet x y) :=
  Domain.subset_dec

class ValueDomain (α : Type)
extends Add α, Mul α, Sub α, BoundedLattice α, ToString α
where
  new : α
  from_const : Int → α
  -- interval [a, b]
  rand : Int → Int → α
  -- Nat : number of iterations
  widen : Nat → α → α → α
  -- Nat : number of iterations
  narrow : Nat → α → α → α
  subset_dec : DecidableRel (fun x y => x = meet x y)
  is_bot_dec : DecidablePred (· = bot)
  -- TODO: backward operations, comparisons

instance (α : Type) [ι : ValueDomain α] :
  DecidablePred (· = ι.bot) :=
  ValueDomain.is_bot_dec

instance (α : Type) [ι : ValueDomain α] :
  DecidableRel (fun x y => x = ι.meet x y) :=
  ValueDomain.subset_dec

-- TODO:
-- constants, intervals, build a non-relational domain from value domains

-- TODO:
-- should the classes be parameterized by the constants and variables
-- of the program, or should it go into the type ?
