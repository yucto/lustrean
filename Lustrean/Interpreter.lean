import Lustrean.Common
import Lustrean.Facts
import Lustrean.Domain

structure PreNode (nb_var : Nat) : Type where
  id : Nat
  out_nodes : List (Nat × inst nb_var)

structure Node (nb_var nb_arcs : Nat) : Type where
  in_nodes : List (Fin nb_arcs)

structure Arc (nb_var nb_nodes : Nat) : Type where
  src : Fin nb_nodes
  dst : Fin nb_nodes
  inst : inst nb_var

structure Cfg (nb_var : Nat) : Type where
  nb_nodes : Nat
  nb_arcs : Nat
  nodes : Array (Node nb_var nb_arcs)
  Hnodes : nb_nodes = nodes.size
  arcs : Array (Arc nb_var nb_nodes)
  Harcs : nb_arcs = arcs.size

namespace Cfg
  variable {nb_var : Nat}

  namespace new
    variable (nb_nodes nb_arcs : Nat)

    def find_nb_arcs (l : List (PreNode nb_var)) : Nat :=
      List.foldl (fun n pn => n + pn.out_nodes.length) 0 l

    theorem find_nb_arcs_incr : ∀ (l : List (PreNode nb_var)) (n m : Nat),
      n ≤ m →
      List.foldl (fun n pn => n + pn.out_nodes.length) n l ≤
        List.foldl (fun n pn => n + pn.out_nodes.length) m l
    := by
      intros l
      induction l <;> intros n m H
      case nil => assumption
      case cons _ _ IH =>
        apply IH
        simp
        assumption

    theorem find_nb_arcs_add : ∀ (l : List (PreNode nb_var)) (n m : Nat),
      List.foldl (fun n pn => n + pn.out_nodes.length) n l + m
        = List.foldl (fun n pn => n + pn.out_nodes.length) (n + m) l
    := by
      intros l
      induction l <;> intros n m <;> simp
      case cons pn' l IH =>
        rw [IH]
        have : n + pn'.out_nodes.length + m = n + m + pn'.out_nodes.length := by
          conv =>
            lhs
            rw [Nat.add_assoc]
            arg 2
            rw [Nat.add_comm]
          rw [←Nat.add_assoc]
        rw [this]

    theorem find_nb_arcs_cons : ∀ (l : List (PreNode nb_var)) (pn : PreNode nb_var),
      find_nb_arcs l + pn.out_nodes.length = find_nb_arcs (pn :: l) :=
    by
      intros l pn
      simp [find_nb_arcs, find_nb_arcs_add]

    structure NewAux (nb_var nb_nodes nb_arcs : Nat) (l : List (PreNode nb_var)) : Type where
      nodes : Array (Node nb_var nb_arcs)
      Hnodes : nb_nodes = nodes.size
      arcs : Array (Arc nb_var nb_nodes)
      Harcs : find_nb_arcs l = arcs.size

    def init : NewAux nb_var nb_nodes nb_arcs [] :=
      .mk (Array.mkArray nb_nodes (.mk [])) (by simp) #[] rfl

    structure StepAux (nb_var nb_nodes nb_arcs : Nat)
      (l : List (PreNode nb_var))
      (out : List (Nat × inst nb_var)) : Type
    where
      nodes : Array (Node nb_var nb_arcs)
      Hnodes : nb_nodes = nodes.size
      arcs : Array (Arc nb_var nb_nodes)
      Harcs : find_nb_arcs l + out.length = arcs.size

    def step.init (l : List (PreNode nb_var))
      (cfg : NewAux nb_var nb_nodes nb_arcs l) :
      StepAux nb_var nb_nodes nb_arcs l []
    := .mk cfg.nodes cfg.Hnodes cfg.arcs cfg.Harcs

    def step.aux (l : List (PreNode nb_var)) (i : Fin nb_nodes)
      (out_node : Nat)
      (out_inst : inst nb_var)
      (Hout : out_node < nb_nodes)
      (out_nodes : List (Nat × inst nb_var))
      (Harcs : find_nb_arcs l + out_nodes.length < nb_arcs)
      (cfg : StepAux nb_var nb_nodes nb_arcs l out_nodes) :
      StepAux nb_var nb_nodes nb_arcs l ((out_node, out_inst) :: out_nodes)
    :=
      let dst := .mk out_node Hout
      let arc := .mk i dst out_inst
      let H : cfg.arcs.size < nb_arcs := by
        rw [←cfg.Harcs]
        assumption
      let arc_idx := .mk cfg.arcs.size H
      let arcs := cfg.arcs.push arc
      let Harcs : find_nb_arcs l + ((out_node, out_inst) :: out_nodes).length = arcs.size := by
        simp [arcs, ←Nat.add_assoc]
        apply cfg.Harcs
      let old_in_arcs := (cfg.nodes.get (cfg.Hnodes ▸ dst)).in_nodes
      let new_node := .mk (arc_idx :: old_in_arcs)
      let nodes := cfg.nodes.set (cfg.Hnodes ▸ dst) new_node
      let Hnodes : nb_nodes = nodes.size := by
        simp [nodes, cfg.Hnodes]
      .mk nodes Hnodes arcs Harcs

    def step.run (l : List (PreNode nb_var)) (i : Fin nb_nodes)
      (out_nodes : List (Nat × inst nb_var))
      (Hn : ∀ p, p ∈ out_nodes → p.fst < nb_nodes)
      (Harcs : find_nb_arcs l + out_nodes.length ≤ nb_arcs)
      (cfg : NewAux nb_var nb_nodes nb_arcs l) :
      StepAux nb_var nb_nodes nb_arcs l out_nodes
    := match out_nodes with
    | [] => step.init nb_nodes nb_arcs l cfg
    | (out_node, out_inst) :: out_nodes =>
      let Hl : find_nb_arcs l + out_nodes.length ≤ nb_arcs := by
        simp at Harcs
        rw [←Nat.add_assoc] at Harcs
        apply Nat.le_trans
        · apply Nat.le_succ
        · assumption
      let cfg := step.run l i out_nodes (by
        intros p Hp
        apply Hn
        simp [Hp]
      ) Hl cfg
      step.aux nb_nodes nb_arcs l i out_node out_inst (by
        let H := Hn (out_node, out_inst)
        simp at H
        assumption
      ) out_nodes Harcs cfg

    def step (l : List (PreNode nb_var))
      (i : Fin nb_nodes) (cfg : NewAux nb_var nb_nodes nb_arcs l)
    (pn : PreNode nb_var) (Hn : pn.id = i ∧ (
      ∀ p, p ∈ pn.out_nodes → p.fst < nb_nodes
    ))
    (Harcs : find_nb_arcs l + pn.out_nodes.length ≤ nb_arcs)
    : NewAux nb_var nb_nodes nb_arcs (pn :: l)
    :=
      let cfg := step.run nb_nodes nb_arcs l i pn.out_nodes Hn.right Harcs cfg
      let Heq : find_nb_arcs l + pn.out_nodes.length = find_nb_arcs (pn :: l) := by
        apply find_nb_arcs_cons
      .mk cfg.nodes cfg.Hnodes cfg.arcs (Heq ▸ cfg.Harcs)

    def aux (l : List (PreNode nb_var))
      (Hlength : List.length l ≤ nb_nodes)
      (Harcs : find_nb_arcs l ≤ nb_arcs)
      (Hsorted : ∀ (i : Fin l.length), (l.get i).id = (i + nb_nodes - List.length l) ∧ (
        ∀ p, p ∈ (l.get i).out_nodes → p.fst < nb_nodes
      )) : NewAux nb_var nb_nodes nb_arcs l
    := match l with
    | [] => init nb_nodes nb_arcs
    | pn :: l =>
      let Ha : find_nb_arcs l ≤ nb_arcs := by
        simp [find_nb_arcs] at Harcs
        simp [find_nb_arcs]
        apply Nat.le_trans
        · apply find_nb_arcs_incr
          apply Nat.zero_le pn.out_nodes.length
        · assumption
      let Hl : l.length ≤ nb_nodes := by
        apply Nat.le_trans
        · apply Nat.le_succ
        · assumption
      let cfg := aux l Hl Ha (by
        intros i
        let H := Hsorted i.succ
        simp at Hlength
        have Hl' : l.length + 1 ≤ nb_nodes + 1 := by
          rw [Nat.add_le_add_iff_right]
          assumption
        have : i + nb_nodes - l.length = i.succ + nb_nodes - (pn :: l).length := by
          simp
          conv =>
            rhs
            rw [Nat.add_assoc]
            lhs
            rhs
            rw [Nat.add_comm]
          conv =>
            rhs
            rw [Nat.add_sub_assoc Hl']
            simp
            rw [←Nat.add_sub_assoc Hl]
        simp at H
        simp
        rw [this]
        assumption
      )
      let i : Fin nb_nodes := .mk (nb_nodes - List.length (pn :: l)) <| by
        simp [Hsorted]
        apply Nat.sub_lt
        · apply Nat.le_trans
          · apply Nat.zero_lt_succ l.length
          · assumption
        · simp
      let Heq : find_nb_arcs l + pn.out_nodes.length = find_nb_arcs (pn :: l) := by
        apply find_nb_arcs_cons
      step nb_nodes nb_arcs l i cfg pn (by
        simp at Hsorted
        let H := Hsorted 0
        simp at H
        simp
        assumption
      ) (Heq ▸ Harcs)
  end new

  def new (l : List (PreNode nb_var)) : Option (Cfg nb_var) :=
    let lsorted := l.mergeSort (fun n₁ n₂ => if n₁.id ≤ n₂.id then true else false)
    if Hsorted : ∀ (i : Fin lsorted.length), (lsorted.get i).id = i ∧ (
        ∀ p, p ∈ (lsorted.get i).out_nodes → p.fst < lsorted.length
      )
    then
      let nb_arcs := new.find_nb_arcs lsorted
      let Hl : l.length = lsorted.length := by
        simp [lsorted, List.mergeSort_length]
      let aux := new.aux l.length nb_arcs lsorted (by simp [Hl])
        (by simp [nb_arcs]) <| by
        rw [Hl]
        intros i
        rw [Nat.add_sub_cancel]
        apply Hsorted
      .some (.mk l.length nb_arcs aux.nodes aux.Hnodes aux.arcs <| by
        simp [nb_arcs]
        apply aux.Harcs
      )
    else .none

  -- TODO: do better
  -- true : should widen, false : shouldn't
  def get_widening_points {nb_var : Nat} (cfg : Cfg nb_var) : { arr : Array Bool // arr.size = cfg.nb_nodes }
  :=
    let arr := Array.mkArray cfg.nb_nodes true
    let Harr : arr.size = cfg.nb_nodes := by
      simp [arr]
    ⟨ arr, Harr ⟩
end Cfg

structure State (α : Type) [ι : Domain α] (cfg : Cfg ι.nb_var) where
  node_env : Array α -- holds an environment at each node
  Hnode_env : node_env.size = cfg.nb_nodes
  arc_env : Array α -- holds [[arc.inst]](env) for each arc where env is the environment at arc.src
  Harc_env : arc_env.size = cfg.nb_arcs
  widening_points : Array Bool
  Hwidening_points : widening_points.size = cfg.nb_nodes
  nb_step : Nat

namespace State
  variable {α : Type} [ι : Domain α] {cfg : Cfg ι.nb_var}

  def get_node_env (s : State α cfg) (i : Fin cfg.nb_nodes) : α :=
    s.node_env.get (s.Hnode_env ▸ i)

  def set_node_env (i : Fin cfg.nb_nodes) (a : α) : StateM (State α cfg) Unit := do
    let s ← get
    let node_env := s.node_env.set (s.Hnode_env ▸ i) a
    let Hnode_env : node_env.size = cfg.nb_nodes := by
      rw [←s.Hnode_env]
      simp [node_env]
    set ({ s with node_env := node_env, Hnode_env := Hnode_env})

  def get_arc_env (s : State α cfg) (i : Fin cfg.nb_arcs) : α :=
    s.arc_env.get (s.Harc_env ▸ i)

  def set_arc_env (i : Fin cfg.nb_arcs) (a : α) : StateM (State α cfg) Unit := do
    let mut s ← get
    let arc_env := s.arc_env.set (s.Harc_env ▸ i) a
    let Harc_env : arc_env.size = cfg.nb_arcs := by
      simp [arc_env, s.Harc_env]
    set ({ s with arc_env := arc_env, Harc_env := Harc_env})

  def iter_arc (arc_idx : Fin cfg.nb_arcs) : StateM (State α cfg) Bool := do
    let s ← get
    let arc := cfg.arcs.get (cfg.Harcs ▸ arc_idx)
    let src_env := s.get_node_env arc.src
    let old_env := s.get_arc_env arc_idx
    let new_env := match arc.inst with
    | .skip => src_env
    | .assign var expr => ι.assign src_env var expr
    | .guard b  => ι.guard src_env b
    set_arc_env arc_idx new_env
    let _ := ι.eq_dec
    let _ := ι.is_subset_dec
    let modified := decide ¬ ι.is_subset old_env new_env
    return modified

  def iter_node (node_idx : Fin cfg.nb_nodes) : StateM (State α cfg) Unit := do
    let s ← get
    let node := cfg.nodes.get (cfg.Hnodes.symm ▸ node_idx)
    let in_env := List.foldl (fun acc_env arc_idx =>
      let env := s.get_arc_env arc_idx
      ι.join acc_env env
    ) ι.bot node.in_nodes
    let s ← get
    if s.widening_points.get (s.Hwidening_points ▸ node_idx)
    then
      let old_env := s.get_node_env node_idx
      set_node_env node_idx (ι.widen old_env in_env s.nb_step)
    else
      set_node_env node_idx in_env
    return

  def iter : StateM (State α cfg) Bool := do
    let mut result := false
    for h : i in [0:cfg.nb_arcs] do
      let b ← iter_arc <| .mk i <| by
        apply Membership.get_elem_helper
        · assumption
        · rfl
      result := result || b
    for h : i in [0:cfg.nb_nodes] do
      iter_node <| .mk i <| by
        apply Membership.get_elem_helper
        · assumption
        · rfl
    let s ← get
    set ({ s with nb_step := s.nb_step.succ })
    return result

  partial def loop : StateM (State α cfg) Unit := do
    let b ← iter
    if b then loop

  def init : State α cfg :=
    let node_env := Array.mkArray cfg.nb_nodes ι.bot
    let Hnode_env : node_env.size = cfg.nb_nodes := by
      simp [node_env]
    let arc_env := Array.mkArray cfg.nb_arcs ι.bot
    let Harc_env : arc_env.size = cfg.nb_arcs := by
      simp [arc_env]
    let widening_points := cfg.get_widening_points
    .mk node_env Hnode_env
      arc_env Harc_env
      widening_points.val widening_points.property 0

  def run (cfg : Cfg ι.nb_var) : State α cfg :=
    (StateT.run loop init).2
end State
