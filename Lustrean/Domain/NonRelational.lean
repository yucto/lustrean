import Lustrean.Facts
import Lustrean.Domain.Domain
import Batteries.Data.Vector
import Lustrean.Domain.NonRelational.ValueDomain
import Lustrean.Domain.NonRelational.Basic
import Lustrean.Domain.NonRelational.JoinLemmas
import Lustrean.Domain.NonRelational.MeetLemmas
import Lustrean.Domain.NonRelational.Lattice
import Lustrean.Domain.NonRelational.Narrow
import Lustrean.Domain.NonRelational.Widen
import Misc

open Batteries (Vector)

namespace Lustrean

namespace NonRelational
  variable {α : Type} {n : Nat}
  variable [ι : ValueDomain α]
  variable (x : NonRelational α n)

  def get (i : Fin n) : α := match x with
  | .non_rel x => x.val.get i
  | .bot => ⊥

  def update (i : Fin n) (a : α) : NonRelational α n :=
    x.map_nil fun x => x.set i a

  def eval : IExpr n → α
  | .nil => ι.nil
  | .var i => get x i
  | .rand a b => ι.rand a b
  | .neg e => - eval e
  | .binop e₁ op e₂ =>
    let i₁ := eval e₁
    let i₂ := eval e₂
    match op with
    | .iadd => i₁ + i₂
    | .isub => i₁ - i₂
    | .imul => i₁ * i₂
    | .idiv => i₁ / i₂

  def assign (i : Fin n) (e : IExpr n) : NonRelational α n :=
    update x i (eval x e)

  def backward_eval (x : NonRelational α n) (e : IExpr n) (r : α) :
    NonRelational α n
  :=
    have : DecidableEq α := ι.eq_dec -- help class inference
    match e with
    | .nil => if ι.is_bot (ι.meet r ι.nil)
      then BoundedLattice.bot
      else x
    | .var i => update x i (ι.meet (get x i) r)
    | .rand a b => if ι.is_bot (ι.meet r (ι.rand a b))
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
    new := coalesce (Vector.mkVector n ValueDomain.new)
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
end Lustrean
