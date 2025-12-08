import Lustrean.Domain.NonRelational.ValueDomain
import Misc

namespace Lustrean
inductive NonRelational (α : Type) [ValueDomain α] (n : Nat) where
| non_rel (env : { env : Vector α n // ∀ i : Fin n, env.get i ≠ ⊥ }) : NonRelational α n
| bot : NonRelational α n
deriving DecidableEq

namespace NonRelational
variable {α : Type} {n : Nat}
variable [ι : ValueDomain α]
variable (x y : NonRelational α n)

instance : DecidableEq (NonRelational α n) := by
  intros x y
  cases x <;> cases y <;> simp
  have : DecidableEq α := ι.eq_dec
  all_goals exact inferInstance

protected def toString : NonRelational α n → String
  | .bot => "⊥"
  | .non_rel env => toString env.val.toArray

instance : ToString (NonRelational α n) where
  toString := NonRelational.toString

def coalesce (env : Vector α n) : NonRelational α n :=
  have := fun i : Fin n => ι.eq_dec (env.get i) ⊥
  if H : ∀ i, env.get i ≠ ⊥
  then
    .non_rel <| .mk env H
  else
    .bot

def mapNil (f : Vector α n → Vector α n) : NonRelational α n :=
  match x with
  | .non_rel x => coalesce <| f x.val
  | .bot => .bot

def map2Nil (f : Vector α n → Vector α n → Vector α n) : NonRelational α n :=
  match x, y with
  | .non_rel x, .non_rel y => coalesce (f x.val y.val)
  | _, _ => .bot

protected def add :=
  map2Nil x y fun x y => Vector.ofFn fun i => x.get i + y.get i

instance : Add (NonRelational α n) where
  add := NonRelational.add

protected def neg :=
  mapNil x fun x => Vector.ofFn fun i => -x.get i

instance : Neg (NonRelational α n) where
  neg := NonRelational.neg

protected def sub :=
  map2Nil x y fun x y => Vector.ofFn fun i => x.get i - y.get i

instance : Sub (NonRelational α n) where
  sub := NonRelational.sub

protected def mul :=
  map2Nil x y fun x y => Vector.ofFn fun i => x.get i * y.get i

instance : Mul (NonRelational α n) where
  mul := NonRelational.mul

protected def div :=
  map2Nil x y fun x y => Vector.ofFn fun i => x.get i / y.get i

instance : Div (NonRelational α n) where
  div := NonRelational.div

theorem join_neq_bot : ∀ (x y : { env : Fin n → α // ∀ i, env i ≠ ⊥}) i,
  x.val i ⊔ y.val i ≠ ⊥ := by
  intros x y i
  let ⟨y, H⟩ := y
  simp [BoundedLattice.join_eq_bot_iff_bot]
  intros
  apply H

def top : NonRelational α n := .non_rel <| .mk (Vector.replicate _ ⊤) fun _ => by
  simp
  apply ι.non_trivial

def join : NonRelational α n := match x, y with
  | .non_rel ⟨x, H⟩, .non_rel ⟨y, _⟩ =>
    .non_rel <| .mk (Vector.ofFn fun i => x.get i ⊔ y.get i) <| (by
      intros i
      simp [BoundedLattice.join_eq_bot_iff_bot]
      intro
      exfalso
      apply H
      assumption)
  | .bot, z | z, .bot => z

def meet : NonRelational α n := map2Nil x y fun x y => Vector.ofFn fun i => x.get i ⊓ y.get i
end NonRelational
end Lustrean
