namespace Lustrean

variable {A C: Type}[instLEAbstract: LE A][Std.IsPartialOrder A]
                    [instLEConcrete: LE C][Std.IsPartialOrder C]
local notation a "≤a" b => instLEAbstract.le a b
local notation a "≤c" b => instLEConcrete.le a b

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

  def IsBestBinAbstraction (f: C → C → C) (g: A → A → A) :=
   ∀ a a', f (concrete a) (concrete a') = concrete (g a a')

end GaloisConnection


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
