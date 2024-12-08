import Lustrean.Parsing.Reify
import Lustrean.Parsing.Inline
import Lustrean.Parsing.Indicise

open Lean
open Elab (liftMacroM)
open Elab.Command (liftTermElabM)
open Core (CoreM)

namespace Lustrean.Parsing

def elab_lustre (nodes : TSyntaxArray `lustre_node) : CoreM Unit := do
  let nodes ← Indicise.elab_lustre <|
    ← Inline.elab_lustre <|
    ← Reify.elab_lustre <|
    nodes
  for nod in nodes do
    println! s!"{nod.value}\n"

elab_rules : command
  | `(command| lustre $nodes:lustre_node*) => do
    let nodes ← nodes.mapM fun nod => do
      let nod ← liftMacroM <| expandMacros nod.raw
      return .mk nod
    liftTermElabM <| elab_lustre nodes

lustre
  node f(x) = o where
    o = x

  node g() = o where
    o = f(5) + f(5)

lustre
  node e₁(x) = o
    guard
      x ≥ 0
    where
      o = 3 + x * [2, ∞]
    assert
      o ≠ 0

  node e₂(x) = o where
    v = e₁(x)
    o = v + v

  node e₃(x) = o where
    v = e₂(x)
    o = v + v

  node e₄(x) = o
    guard
      x ≥ 0
    where
      o = v + v
      v = e₃(x)
    assert
      o ≥ 0

  -- node main() = o where
  --   o = e₄(5)


lustre
  node a() = o₁, o₂ where
    o₁ = 3
    o₂ = 5

  node b() = o₁ where
    o₁, o₂ = a()

end Lustrean.Parsing

-- node main' = o where
--     o : nat = o₄
--     o₄ : nat = v₄ + v₄
--     v₄ : nat = o₃
--     o₃ : nat = v₃ + v₃
--     v₃ : nat = o₂
--     o₂ : nat = v₂ + v₂
--     v₂ : nat = o₁
--     o₁ : nat = 3
-- 
