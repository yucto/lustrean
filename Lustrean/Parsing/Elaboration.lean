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

end Lustrean.Parsing
