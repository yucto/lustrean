import Lustrean.Parsing.Reify
import Lustrean.Parsing.Inline
import Lustrean.Parsing.Indicise
import Lustrean.Parsing.Normalize
import Lustrean.Parsing.Compile
import Lustrean.Interpreter
import Lustrean.Domain.Interval

open Lean
open Elab (liftMacroM)
open Elab.Command (liftTermElabM)
open Core (CoreM)

namespace Lustrean.Parsing


lustre
  node u(x) = o
    where
      o = x
    assert
      x ≤ 0

lustre
  node f(c, z) = y where
    y = if c = 0 then x else z
    x = if c = 0 then z else y

lustre
  node f() = x where
    x = y
    y = x

lustre
  node u(x) = o where
    o = 0 fby x

  node f(x) = o
    guard
      x ≥ 0
    where
      o = if x > 3 then 3 else x
    assert
      0 ≤ x ∧ x ≤ 3

  node g() = o where
    o = f(5) + f(5)

  node h() where
    o = 0 fby 1 fby o+1
    i =
      if o = 5 then
        if 0 ≠ 0 then 1 else 2
      else
        0

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

  def elab_lustre (nodes : TSyntaxArray `lustre_node) : CoreM Unit := do
    let nodes :=
      Compile.elab_lustre <|
      Normalize.elab_lustre <|
      ← Indicise.elab_lustre <|
      ← Inline.elab_lustre <|
      ← Reify.elab_lustre <|
      nodes
    for ⟨n, vertices, output_vars⟩ in nodes do
      let some cfg := Cfg.new vertices | continue
      -- println! s!"{cfg.arcs}"
      let state ← State.run (m := CoreM) (α := NonRelational (Undefined (Interval [])) n) cfg
      -- println! "Step ∞"
      -- for (env, i) in state.node_env.zipWithIndex do
        -- println! s!" {i}) {env}"
      let some env := state.node_env.back? | continue
      for (⟨var, ref⟩, i) in output_vars.zipWithIndex do
        let val := env.get var
        -- println! s!"Checking {i}-th variable {var}: {val}..."
        if val.may_be_nil then
          logErrorAt ref "this variable could be nil"
          -- println! s!"  The {i}-th output variable can be nil."

  elab_rules : command
    | `(command| lustre $nodes:lustre_node*) => do
      let nodes ← nodes.mapM fun nod => do
        let nod ← liftMacroM <| expandMacros nod.raw
        return .mk nod
      liftTermElabM <| elab_lustre nodes
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
