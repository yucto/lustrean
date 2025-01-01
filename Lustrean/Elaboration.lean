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
      println! "Step ∞"
      for (env, i) in state.node_env.zipWithIndex do
        println! s!" {i}) {env}"
      let some env := state.node_env.back? | continue
      for ⟨var, ref⟩ in output_vars do
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
end Lustrean.Elaboration
