import Lustrean.Elaboration.Normalize
import Lustrean.Imp
import Misc.Lean

open Lean
namespace Lustrean.Elaboration.Compile
open Normalize
section
variable {n m : Nat}

def _root_.Lustrean.Elaboration.Normalize.SimpleExpr.to_cfg_expr : SimpleExpr n m → IExpr (1 + n + m + m)
  | .interval lb ub =>
    let lb := match lb with
      | .minf => none
      | .nat n => some n
    let ub := match ub with
      | .pinf => none
      | .nat n => some n
    .rand lb ub
  | .bin_op op l r =>
    let op := match op with
      | .add => .iadd
      | .mul => .imul
      | .sub => .isub
    .binop l.to_cfg_expr op r.to_cfg_expr
  | .var .step => .var <| .mk 0 <| by omega
  | .var (.input_var k) => .var <| .mk (1+k) <| by omega
  | .var (.bound_var k) => .var <| .mk (1+n+k) <| by omega
  | .var (.old_bound_var k) => .var <| .mk (1+n+m+k) <| by omega

def _root_.Lustrean.Elaboration.Normalize.BoolExpr.to_cfg_expr : BoolExpr n m → BExpr (1 + n + m + m)
  | .cmp_op op l r =>
    let op := match op with
      | .eq => .eq
      | .lt => .lt
      | .leq => .le
    .compare l.to_cfg_expr op r.to_cfg_expr
  | .bin_op op l r =>
    let l := l.to_cfg_expr
    let r := r.to_cfg_expr
    match op with
    | .or => .or l r
    | .and => .and l r
end

/-- How many iterations of the main loop to unroll. -/
def unrollLoop : Nat := 1

def elabIntoCfg (nod : Normalize.Node) : CoreM (List (PreNode nod.totalVars) × Array &(Fin nod.totalVars)) :=
  withTraceNode `Lustrean.Elab.Compile (msg := fun e => return m!"{exceptEmoji e} elabExpr\n{nod}\n⇒\n{toMessageData e.toOption}") do
  let mut result := #[
    { id := 0, out_nodes := [{ out_node := 2, out_inst := .assign step (IExpr.const 0)}] },
    { id := 1, out_nodes := [] }
  ]
  for h : i in [0:nod.m] do
    let k := Fin.mk i <| Membership.get_elem_helper h rfl
    result := result.push {
      id := result.size
      out_nodes := [{ out_node :=result.size + 1, out_inst := .assign (bound_var k) .nil}]
    }
  for _ in [0:unrollLoop] do
    for h : i in [0:nod.m] do
      let k := Fin.mk i <| Membership.get_elem_helper h rfl
      result := result.push {
        id := result.size
        out_nodes := [{ out_node := result.size + 1,out_inst := .assign (old_bound_var k) (.var <| bound_var k)}]
      }
    for h : i in [0:nod.n] do
      let k := Fin.mk i <| Membership.get_elem_helper h rfl
      result := result.push {
        id := result.size
        out_nodes := [{ out_node := result.size + 1, out_inst :=  .assign (input_var k) (.rand none none)}]
      }
    for g in nod.guards do
      result := result.push {
        id := result.size
        out_nodes := [{ out_node := result.size + 1,  out_inst := .guard g.to_cfg_expr}]
      }
    for h : i in [0:nod.m] do
      let k := Fin.mk i <| Membership.get_elem_helper h rfl
      result := result.push {
        id := result.size
        out_nodes := [{ out_node := result.size + 1,  out_inst := .assign (bound_var k) .nil}]
      }
    let there_id := result.size
    for h : i in [0:nod.m] do
      let k := Fin.mk i <| Membership.get_elem_helper h rfl
      match nod.bound_vars[i].value with
      | .simple e =>
        result := result.push {
          id := result.size
          out_nodes := [{ out_node := result.size + 1,  out_inst := .assign (bound_var k) e.to_cfg_expr}]
        }
      | .ite cond e₁ e₂ =>
        result := result.push {
          id := result.size
          out_nodes := [
            { out_node := result.size + 1,  out_inst := .guard cond.to_cfg_expr},
            { out_node := result.size + 2,  out_inst := .guard cond.to_cfg_expr.not}
          ]
        }
        result := result.push {
          id := result.size
          out_nodes := [{ out_node := result.size+2,  out_inst := .assign (bound_var k) e₁.to_cfg_expr}]
        }
        result := result.push {
          id := result.size
          out_nodes := [{ out_node := result.size+1,  out_inst := .assign (bound_var k) e₂.to_cfg_expr}]
        }
    result := result.push {
      id := result.size
      out_nodes := [
        { out_node := there_id,  out_inst := .skip},                   -- loop again current iteration
        { out_node := 1,  out_inst := .skip},                          -- exit program
        { out_node := result.size + 1, out_inst := .assign step (.binop (.var step) .iadd (IExpr.const 1))} -- next iteration
      ]
    }
  let here_id := result.size
  for h : i in [0:nod.m] do
    let k := Fin.mk i <| Membership.get_elem_helper h rfl
    result := result.push {
      id := result.size
      out_nodes := [{ out_node := result.size + 1, out_inst := .assign (old_bound_var k) (.var <| bound_var k)}]
    }
  for h : i in [0:nod.n] do
    let k := Fin.mk i <| Membership.get_elem_helper h rfl
    result := result.push {
      id := result.size
      out_nodes := [{ out_node := result.size + 1, out_inst := .assign (input_var k) (.rand none none)}]
    }
  for g in nod.guards do
    result := result.push {
      id := result.size
      out_nodes := [{ out_node := result.size + 1, out_inst := .guard g.to_cfg_expr}]
    }
  for h : i in [0:nod.m] do
    let k := Fin.mk i <| Membership.get_elem_helper h rfl
    result := result.push {
      id := result.size
      out_nodes := [{ out_node := result.size + 1, out_inst := .assign (bound_var k) .nil}]
    }
  let there_id := result.size
  for h : i in [0:nod.m] do
    let k := Fin.mk i <| Membership.get_elem_helper h rfl
    match nod.bound_vars[i].value with
    | .simple e =>
      result := result.push {
        id := result.size
        out_nodes := [{ out_node := result.size + 1, out_inst := .assign (bound_var k) e.to_cfg_expr}]
      }
    | .ite cond e₁ e₂ =>
      result := result.push {
        id := result.size
        out_nodes := [
          { out_node := result.size + 1, out_inst := .guard cond.to_cfg_expr},
          { out_node := result.size + 2, out_inst := .guard cond.to_cfg_expr.not}
        ]
      }
      result := result.push {
        id := result.size
        out_nodes := [{ out_node := result.size+2, out_inst := .assign (bound_var k) e₁.to_cfg_expr}]
      }
      result := result.push {
        id := result.size
        out_nodes := [{ out_node := result.size+1, out_inst := .assign (bound_var k) e₂.to_cfg_expr}]
      }
  result := result.push {
    id := result.size
    out_nodes := [
      { out_node := here_id, out_inst := .assign step (.binop (.var step) .iadd (IExpr.const 1))}, -- go to next iteration
      { out_node := there_id, out_inst := .skip},                   -- loop again current iteration
      { out_node := result.size + 1,  out_inst := .skip}             -- exit program
    ]
  }
  for a in nod.asserts do
    result := result.push {
      id := result.size
      out_nodes := [{ out_node := result.size+1, out_inst := .assert a.value.to_cfg_expr, ref? := a.ref}]
    }
  let exit_id := result.size
  result := result.push {
    id := exit_id
    out_nodes := []
  }
  result := { result with [1] := {
    id := 1
    out_nodes := [
      { out_node := exit_id, out_inst := .skip}
    ]
  }}
  let output_vars := nod.output_vars.map (·.map fun
    | .step => step
    | .input_var k => input_var k
    | .bound_var k => bound_var k
    | .old_bound_var k => old_bound_var k)
  return (result.toList, output_vars)
where
  step : Fin nod.totalVars := .mk 0 (by grind [Normalize.Node.totalVars])
  input_var (k : Fin nod.n) : Fin nod.totalVars := .mk (1+k) (by grind [Normalize.Node.totalVars])
  bound_var (k : Fin nod.m) : Fin nod.totalVars := .mk (1+nod.n+k) (by grind [Normalize.Node.totalVars])
  old_bound_var (k : Fin nod.m) : Fin nod.totalVars := .mk (1+nod.n+nod.m+k) (by grind [Normalize.Node.totalVars])

def elabLustre (a : Array Normalize.Node) : CoreM (Array (Σ n, List (PreNode n) × Array &(Fin n))) :=
  a.mapM fun nod => do return ⟨nod.totalVars, ← elabIntoCfg nod⟩

end Lustrean.Elaboration.Compile

initialize
  registerTraceClass `Lustrean.Elab.Compile (inherited := true)
