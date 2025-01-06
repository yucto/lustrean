import Lustrean.Elaboration.Normalize
import Lustrean.Imp

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
def unroll_loop : Nat := 1

def elab_into_cfg (nod : Normalize.Node) : List (PreNode nod.total_vars) × Array (&Fin nod.total_vars) := Id.run do
  -- TODO: default is a dummy value
  let mut result := #[
    { id := 0, out_nodes := [(2, .assign step (IExpr.const 0), default)] },
    { id := 1, out_nodes := [] }
  ]
  for h : i in [0:nod.m] do
    let k := Fin.mk i <| Membership.get_elem_helper h rfl
    result := result.push {
      id := result.size
      -- TODO: default is a dummy value
      out_nodes := [(result.size + 1, .assign (bound_var k) .nil, default)]
    }
  for _ in [0:unroll_loop] do
    for h : i in [0:nod.m] do
      let k := Fin.mk i <| Membership.get_elem_helper h rfl
      result := result.push {
        id := result.size
        -- TODO: default is a dummy value
        out_nodes := [(result.size + 1, .assign (old_bound_var k) (.var <| bound_var k), default)]
      }
    for h : i in [0:nod.n] do
      let k := Fin.mk i <| Membership.get_elem_helper h rfl
      result := result.push {
        id := result.size
        -- TODO: default is a dummy value
        out_nodes := [(result.size + 1, .assign (input_var k) (.rand none none), default)]
      }
    for g in nod.guards do
      result := result.push {
        id := result.size
        -- TODO: default is a dummy value
        out_nodes := [(result.size + 1, .guard g.to_cfg_expr, default)]
      }
    for h : i in [0:nod.m] do
      let k := Fin.mk i <| Membership.get_elem_helper h rfl
      result := result.push {
        id := result.size
        -- TODO: default is a dummy value
        out_nodes := [(result.size + 1, .assign (bound_var k) .nil, default)]
      }
    let there_id := result.size
    for h : i in [0:nod.m] do
      let k := Fin.mk i <| Membership.get_elem_helper h rfl
      match nod.bound_vars[i].value with
      | .simple e =>
        result := result.push {
          id := result.size
          -- TODO: default is a dummy value
          out_nodes := [(result.size + 1, .assign (bound_var k) e.to_cfg_expr, default)]
        }
      | .ite cond e₁ e₂ =>
        result := result.push {
          id := result.size
          -- TODO: default are dummy values
          out_nodes := [
            (result.size + 1, .guard cond.to_cfg_expr, default),
            (result.size + 2, .guard cond.to_cfg_expr.not, default)
          ]
        }
        result := result.push {
          id := result.size
          -- TODO: default is a dummy value
          out_nodes := [(result.size+2, .assign (bound_var k) e₁.to_cfg_expr, default)]
        }
        result := result.push {
          id := result.size
          out_nodes := [(result.size+1, .assign (bound_var k) e₂.to_cfg_expr, default)]
        }
    result := result.push {
      id := result.size
      -- TODO: default are dummy values
      out_nodes := [
        (there_id, .skip, default),                   -- loop again current iteration
        (1, .skip, default),                          -- exit program
        -- next iteration
        (result.size + 1, .assign step (.binop (.var step) .iadd (IExpr.const 1)), default)
      ]
    }
  let here_id := result.size
  for h : i in [0:nod.m] do
    let k := Fin.mk i <| Membership.get_elem_helper h rfl
    result := result.push {
      id := result.size
      -- TODO: default is a dummy value
      out_nodes := [(result.size + 1, .assign (old_bound_var k) (.var <| bound_var k), default)]
    }
  for h : i in [0:nod.n] do
    let k := Fin.mk i <| Membership.get_elem_helper h rfl
    result := result.push {
      id := result.size
      -- TODO: default is a dummy value
      out_nodes := [(result.size + 1, .assign (input_var k) (.rand none none), default)]
    }
  for g in nod.guards do
    result := result.push {
      id := result.size
      -- TODO: default is a dummy value
      out_nodes := [(result.size + 1, .guard g.to_cfg_expr, default)]
    }
  for h : i in [0:nod.m] do
    let k := Fin.mk i <| Membership.get_elem_helper h rfl
    result := result.push {
      id := result.size
      -- TODO: default is a dummy value
      out_nodes := [(result.size + 1, .assign (bound_var k) .nil, default)]
    }
  let there_id := result.size
  for h : i in [0:nod.m] do
    let k := Fin.mk i <| Membership.get_elem_helper h rfl
    match nod.bound_vars[i].value with
    | .simple e =>
      result := result.push {
        id := result.size
        -- TODO: default is a dummy value
        out_nodes := [(result.size + 1, .assign (bound_var k) e.to_cfg_expr, default)]
      }
    | .ite cond e₁ e₂ =>
      result := result.push {
        id := result.size
        -- TODO: default are dummy values
        out_nodes := [
          (result.size + 1, .guard cond.to_cfg_expr, default),
          (result.size + 2, .guard cond.to_cfg_expr.not, default)
        ]
      }
      result := result.push {
        id := result.size
        -- TODO: default is a dummy value
        out_nodes := [(result.size+2, .assign (bound_var k) e₁.to_cfg_expr, default)]
      }
      result := result.push {
        id := result.size
        out_nodes := [(result.size+1, .assign (bound_var k) e₂.to_cfg_expr, default)]
      }
  result := result.push {
    id := result.size
    -- TODO: default are dummy values
    out_nodes := [
      (here_id, .assign step (.binop (.var step) .iadd (IExpr.const 1)), default), -- go to next iteration
      (there_id, .skip, default),                   -- loop again current iteration
      (result.size + 1, .skip, default)             -- exit program
    ]
  }
  for a in nod.asserts do
    result := result.push {
      id := result.size
      out_nodes := [(result.size+1, .assert a.value.to_cfg_expr, a.ref)]
    }
  let exit_id := result.size
  result := result.push {
    id := exit_id
    out_nodes := []
  }
  result := { result with [1] := {
    id := 1
    out_nodes := [
      (exit_id, .skip, default)
    ]
  }}
  let output_vars := nod.output_vars.map (·.map fun
    | .step => step
    | .input_var k => input_var k
    | .bound_var k => bound_var k
    | .old_bound_var k => old_bound_var k)
  return (result.data, output_vars)
where
  step : Fin nod.total_vars := .mk 0 <| by
    unfold Normalize.Node.total_vars
    omega
  input_var (k : Fin nod.n) : Fin nod.total_vars := .mk (1+k) <| by
    unfold Normalize.Node.total_vars
    omega
  bound_var (k : Fin nod.m) : Fin nod.total_vars := .mk (1+nod.n+k) <| by
    unfold Normalize.Node.total_vars
    omega
  old_bound_var (k : Fin nod.m) : Fin nod.total_vars := .mk (1+nod.n+nod.m+k) <| by
    unfold Normalize.Node.total_vars
    omega

def elab_lustre (a : Array Normalize.Node) : Array (Σ n, List (PreNode n) × Array (&Fin n)) :=
  a.map fun nod =>
    ⟨nod.total_vars, elab_into_cfg nod⟩

end Lustrean.Elaboration.Compile
