import Lustrean.Elaboration.Reify
import Lustrean.Elaboration.Inline
import Lustrean.Elaboration.Indicise
import Lustrean.Elaboration.Normalize
import Lustrean.Elaboration.Compile
import Lustrean.Interpreter
import Lustrean.Domain.Interval

open Lean
open Elab (liftMacroM)
open Elab.Command (liftTermElabM)
open Core (CoreM)

namespace Lustrean.Elaboration
def elabLustre (nodes : TSyntaxArray `lustre_node) : CoreM Unit := do
  let nodes :=
    Compile.elabLustre <|
    Normalize.elabLustre <|
    ← Indicise.elabLustre <|
    ← Inline.elabLustre <|
    ← Reify.elabLustre <|
    nodes
  for ⟨n, vertices, output_vars⟩ in nodes do
    let some cfg := Cfg.new vertices | continue
    -- println! s!"{cfg.arcs}"
    let state ← State.run (m := CoreM) (α := NonRelational (Undefined (Interval [])) n) cfg
    -- println! "Step ∞"
    -- for (env, i) in state.node_env.zipWithIndex do
    --   println! s!" {i}) {env}"
    let some env := state.node_env.back? | continue
    for ⟨var, ref⟩ in output_vars do
      let val := env.get var
      -- println! s!"Checking {i}-th variable {var}: {val}..."
      if val.may_be_nil then
        logErrorAt ref s!"variable {ref.getId} could be nil"
        -- println! s!"  The {i}-th output variable can be nil."

elab_rules : command
  | `(command| lustre $nodes:lustre_node*) => do
    let nodes ← nodes.mapM fun nod => do
      let nod ← liftMacroM <| expandMacros nod.raw
      return .mk nod
    liftTermElabM <| elabLustre nodes
end Lustrean.Elaboration
