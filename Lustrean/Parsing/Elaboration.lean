import Lustrean.Parsing.Phase2

open Lean.Elab.Command (liftTermElabM)

namespace Lustrean.Parsing

elab_rules : command
  | `(command| lustre $nodes:lustre_node*) =>
    for nod in nodes do
      let nod1 ← liftTermElabM <| Phase1.elab_node nod
      let _nod2 ← liftTermElabM <| Phase2.elab_node nod1

lustre
  node hello(x : nat, y : nat) = o where
    o : nat = x + y

end Lustrean.Parsing
