namespace Lustrean

/-!
# Galois Connection

See [wikipedia](https://en.wikipedia.org/wiki/Galois_connection).

A Galois connection between two partially ordered sets A and C
(called respectively _abstract domain_ and _concrete domain_)
is a pair of functions α: C → A and γ: A → C such that

                ∀ a c, α c ≤ a ↔ c ≤ γ a

The function α gives an abstract representation to the concrete
element c, while γ gives the concrete representation of the
abstract element α. In practice, abstract domains act as a type
of approximation of the elements in the concrete domain. The
previous condition guarantees that α gives the best abstraction
possible for any c, that is

                  α c = ⊓ { a : A // c ≤ γ a }

where ⊔ identifies the greatest lower bound (if it exists).

Galois connections are relevant in abstract interpretation since
they give a relation between the domain we want to reason about
and the approximation we are able to do so with.
-/

variable {A C: Type}[instLEAbstract: LE A][Std.IsPartialOrder A]
                    [instLEConcrete: LE C][Std.IsPartialOrder C]
local notation a "≤a" b => instLEAbstract.le a b
local notation a "≤c" b => instLEConcrete.le a b

/-- There exists concrete and abstract functions between
partial orders A and C -/
class GaloisConnection(A C: Type)[LE A][LE C] where
  concrete: A → C
  abstract: C → A

  connection: ∀ {a c}, abstract c ≤ a ↔ c ≤ concrete a
export GaloisConnection (concrete abstract)


namespace GaloisConnection
  variable [connection: GaloisConnection A C]

  theorem abstract_concrete_reductive (a: A)
  : abstract (concrete a : C) ≤ a
  := by
    apply GaloisConnection.connection.mpr
    apply Std.IsPreorder.le_refl

  theorem concrete_abstract_extensive (c: C)
  : c ≤ concrete (abstract c : A)
  := by
    apply GaloisConnection.connection.mp
    apply Std.IsPreorder.le_refl

  theorem abstract_monotone (c c': C)
  : c ≤ c' → (abstract c) ≤a (abstract c')
  := by
    intros c_c'
    apply GaloisConnection.connection.mpr
    calc c
      _ ≤ c' := c_c'
      _ ≤ (concrete (abstract c')) := by apply concrete_abstract_extensive

  theorem concrete_monotone (a a': A)
  : a ≤ a' → (concrete a) ≤c (concrete a')
  := by
    intros a_a'
    apply GaloisConnection.connection.mp
    calc _
      _ ≤ a := by apply abstract_concrete_reductive
      _ ≤ a' := a_a'

  def IsAbstraction (f: C → C) (g: A → A) :=
   ∀ a, f (concrete a) ≤ concrete (g a)

  def IsBestAbstraction (f: C → C) (g: A → A) :=
   ∀ a, f (concrete a) = concrete (g a)

  def IsBinAbstraction (f: C → C → C) (g: A → A → A) :=
   ∀ a a', f (concrete a) (concrete a') ≤ concrete (g a a')

  def IsBestBinAbstraction (f: C → C → C) (g: A → A → A) :=
   ∀ a a', f (concrete a) (concrete a') = concrete (g a a')

end GaloisConnection


/-- A Galois embedding is a Galois connection for which
concreticising and abstracting successively over an abstract
element does not make us loose precision. As a useful corolary,
if the concretization of two abstract elements are related in
a concrete domain of a Galois embedding, they are related in
the abstract domain. This can be useful in proofs, since it's
easier to reason in the concrete domain.  -/
class GaloisEmbedding(A C: Type)[LE A][LE C]
extends GaloisConnection A C
where
  embedding: ∀ a, abstract (concrete a) = a

attribute [simp] GaloisEmbedding.embedding

namespace GaloisEmbedding
  variable [emb: GaloisEmbedding A C]
  theorem lt_of_concrete_lt (a a': A): (concrete a ≤c concrete a') → a ≤a a'
  := by
    intros concr_lt
    rewrite [←emb.embedding a, ←emb.embedding a']
    apply emb.toGaloisConnection.abstract_monotone
    exact concr_lt
end GaloisEmbedding
