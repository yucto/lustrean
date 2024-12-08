import Lustrean.Domain
import Aesop

inductive inst (n : Nat) : Type :=
| skip : inst n
| assign : Fin n → iexpr n → inst n
| guard : bexpr n → inst n

namespace Array
  def All {α : Type} (P : α → Prop) (as : Array α): Prop :=
    ∀ (i : Fin as.size), P (as.get i)

  instance {α : Type} (P : α → Prop) [DecidablePred P] (as : Array α) :
    Decidable (All P as)
  := by
    unfold All
    apply Nat.decidableForallFin

  theorem All.empty {α : Type} (P : α → Prop) : All P #[] := by
    intros i
    cases i.isLt

  theorem All.push {α : Type} (P : α → Prop) (as : Array α) (a : α):
    All P as → P a → All P (as.push a)
  := by
    intros Has Ha i
    simp
    rw [Array.get_push]
    split
    · apply Has
    · assumption

  theorem All.extract.loop {α : Type} (P : α → Prop) (as : Array α) (i j : Nat)
    (bs : Array α) : All P as → All P bs → All P (Array.extract.loop as i j bs)
  := by
    intros Has
    revert bs
    revert j
    unfold Array.extract.loop
    induction i <;> intros j bs Hbs
    <;> split <;> rename_i h
    <;> try assumption
    rename_i i IH
    simp
    have Hb' : All P (bs.push as[j]) := by
      apply All.push <;> try assumption
      apply Has
    specialize IH j.succ (bs.push (as.get ⟨j, h⟩)) Hb'
    unfold Array.extract.loop
    apply IH

  theorem All.extract {α : Type} (P : α → Prop) (as : Array α) (i j : Nat) :
    All P as → All P (as.extract i j)
  := by
    intros Has
    unfold Array.extract
    apply All.extract.loop
    · assumption
    · apply All.empty

  def foldip.aux {α β : Type} (P : α → Prop) (n : Nat) (as : Array α)
    (HAll : All P as) (f : Fin as.size → β → ∀ (a : α), P a → β) (init : β)
    (Heq : as.size = n) : β
  := match n with
  | 0 => init
  | n + 1 => f (Heq ▸ 0) (foldip.aux P n (as.extract 1 as.size)
    (by apply All.extract <;> assumption)
    (fun i =>
      let Hi : (as.extract 1 as.size).size = n := by
        simp
        rw [Heq]
        simp
      (Heq ▸ f) (Hi ▸ i).succ
    )
    init
    (by
      simp
      rw [Heq]
      simp
    )
  ) (as.get (Heq ▸ 0)) (HAll (Heq ▸ 0))

  def foldip {α : Type} (as : Array α) (P : α → Prop) (HAll : All P as)
    {β : Type} (f : Fin as.size → β → ∀ (a : α), P a → β) (init : β) : β
  := foldip.aux P as.size as HAll f init rfl

  def foldp {α : Type} (as : Array α) (P : α → Prop) (HAll : All P as) {β : Type}
    (f : β → ∀ (a : α), P a → β) (init : β) : β
  := foldip as P HAll (fun _ b a p => f b a p) init

  def mapp {α : Type} (as : Array α) (P : α → Prop) (HAll : All P as) {β : Type}
    (f : ∀ (a : α), P a → β) : Array β
  := foldp as P HAll (fun acc a p => acc.push (f a p)) #[]

  theorem mapp_size : ∀ (α β : Type) (as : Array α) (P : α → Prop) (HAll : All P as)
    (f : ∀ (a : α), P a → β), (mapp as P HAll f).size = as.size
  := by
    intros α β as P HAll f
    unfold mapp foldp foldip foldip.proof_1

    have : ∀ (α β : Type) (P : α → Prop) (n : Nat) (as : Array α) (HAll : All P as)
      (f : ∀ (a : α), P a → β), as.size = n → (mapp as P HAll f).size = n :=
    by
      intros α β P n as HAll f Hn
      unfold mapp foldp foldip foldip.aux
      simp
      induction n
      case zero =>

      cases Hn
      symm at Hn
      cases Hn


      rw [Hn]

      simp_all only [eq_mpr_eq_cast, Nat.add_one_sub_one, eq_mp_eq_cast, cast_cast, Array.get_eq_getElem]
      induction n
      case zero =>
        simp
        sorry
      case succ n IH =>
        simp_all only [Nat.add_right_eq_self, Nat.add_one_ne_zero, false_implies]
        sorry
    intros α β as P HAll f
    apply this
    rfl

  def foldi {α : Type} (as : Array α) {β : Type} (f : Fin as.size → β → α → β) (init : β) : β :=
    foldip as (fun _ => True) (fun _ => True.intro) (fun i b a _ => f i b a) init
end Array

namespace List
  def All {α : Type} (P : α → Prop) (l : List α) : Prop :=
    ∀ (a : α), a ∈ l → P a

  theorem All.cons {α : Type} (P : α → Prop) (a : α) (l : List α) :
    All P (a :: l) ↔ P a ∧ All P l
  := by
    constructor <;> intros H
    · constructor
      · apply H
        apply List.Mem.head
      · intros a Ha
        apply H
        apply List.Mem.tail
        assumption
    · cases H
      rename_i Ha Hl
      intros a' Ha'
      cases Ha'
      · assumption
      · apply Hl
        assumption

  def foldip {α β : Type} (l : List α) (P : α → Prop) (HAll : All P l)
    (f : β → ∀ (a : α), P a → β) (init : β) : β :=
  match l with
  | [] => init
  | a :: l =>
    let IH : β := foldip l P (by
      rewrite [All.cons] at HAll
      cases HAll
      assumption
    ) f init
    f IH a <| by
      apply HAll
      constructor
end List

structure pre_node (n : Nat) : Type where
  id : Nat
  out_nodes : List (Nat × inst n)

structure node (n : Nat) (nb_nodes : Nat) : Type where
  out_nodes : List (Fin nb_nodes × inst n)

def get_nodes {nb_var : Nat} (l : List (pre_node nb_var)) : Option ({ arr : Array (node nb_var l.length) // arr.size = l.length }) :=
  let lsorted := l.mergeSort (fun n₁ n₂ => if n₁.id ≤ n₂.id then true else false)
  let as := Array.mk lsorted
  if h : ∀ (i : Fin as.size), (as.get i).id = i ∧ (
    ∀ p, p ∈ (as.get i).out_nodes → p.fst < l.length
  )
  then
    let Hlength : l.length = as.size := by
      rw [←Array.data_length]
      simp
      rw [List.mergeSort_length]
    let arr := Array.mapp as (fun a => a.id < l.length ∧ (
      ∀ p, p ∈ a.out_nodes → p.fst < l.length
    )) (by
      intros i
      specialize h i
      constructor
      · rw [h.left, Hlength]
        apply i.isLt
      · apply h.right
    ) (fun pn Hi =>
      let Hall : ∀ x, x ∈ pn.out_nodes → x.fst < l.length := Hi.right
      let l := List.foldip pn.out_nodes (fun x => x.fst < l.length) Hall (fun l x Hx =>
        (Fin.mk x.fst Hx, x.snd) :: l
      ) []
      node.mk l
    )
    let Harr : arr.size = l.length := by
      simp [Hlength]
      simp [arr]
      apply Array.mapp_size
    .some ⟨ arr, Harr ⟩
  else none

structure cfg : Type where
  nb_var : Nat
  nb_nodes : Nat
  nodes : Array (node nb_var nb_nodes)
  Heq : nodes.size = nb_nodes

structure arc (nb_var : Nat) (nb_nodes : Nat) : Type where
  src : Fin nb_nodes
  dst : Fin nb_nodes
  inst : inst nb_var

namespace cfg
  def new {nb_var : Nat} (l : List (pre_node nb_var)) : Option cfg :=
    match get_nodes l with
    | .none => .none
    | .some ⟨ nodes, Hnodes ⟩ => cfg.mk nb_var l.length nodes Hnodes

  def arcs (cfg : cfg) :
    Array (arc cfg.nb_var cfg.nb_nodes)
  :=
    let l : List (arc cfg.nb_var cfg.nb_nodes) :=
    Array.foldi cfg.nodes  (fun i acc n =>
      let new : List (arc cfg.nb_var cfg.nb_nodes)
      := List.map (fun (x : Fin cfg.nb_nodes × inst cfg.nb_var) =>
        arc.mk /-(TODO: match cfg.Heq with | Eq.refl _ => i)-/
        /-(Eq.rec i cfg.Heq)-/
        (by
          rw [cfg.Heq] at i
          exact i
        )
         x.fst x.snd
      ) n.out_nodes
      new ++ acc
    ) []
    Array.mk l

  -- TODO: do better
  -- true : should widen, false : shouldn't
  def get_widening_points (cfg : cfg) : { arr : Array Bool // arr.size = cfg.nb_nodes }
  :=
    let arr := Array.mkArray cfg.nb_nodes true
    let Harr : arr.size = cfg.nb_nodes := by
      simp [arr]
    ⟨ arr, Harr ⟩
end cfg

structure state (α : Type) [Domain α] (cfg : cfg) where
  node_env : Array α
  Hnode_env : node_env.size = cfg.nb_nodes

namespace state
  variable {α : Type} [ι : Domain α] {cfg : cfg} (s : state α cfg)

  def get (i : Fin cfg.nb_nodes) : α :=
    s.node_env.get (by -- TODO
      rw [s.Hnode_env]
      apply i
    )

  def set (i : Fin cfg.nb_nodes) (a : α) : state α cfg :=
    let node_env := s.node_env.set (by -- TODO
        rw [s.Hnode_env]
        apply i
      ) a
    let Hnode_env : node_env.size = cfg.nb_nodes := by
      rw [←s.Hnode_env]
      simp [node_env]
    state.mk node_env Hnode_env

  def iter (s : state α cfg) : state α cfg :=
    let iter_arc (arc : arc cfg.nb_var cfg.nb_nodes) :=
      let src_env := s.get arc.src
      let dst_env := match s.get arc.inst with
      | .skip => src_env
      | .assign var expr => src_env.assign var expr
      | .guard b  => src_env.guard b
    sorry


/-  def unique {α : Type} (P : α → Prop) : α → Prop :=
    fun (a : α) => P a ∧ ∀ (b : α), P b → a = b

  def dec_forall_fin {n : Nat} (P : Fin n → Prop) [ι : DecidablePred P] :
    Decidable (∀ (i : Fin n), P i)
  := by
    induction n
    · apply isTrue
      intros i
      cases i
      rename_i v Hv
      cases Hv
    · rename_i n IH
      cases (ι 0) <;> rename_i H
      · apply isFalse
        intros Hc
        apply H
        apply Hc
      · cases (IH (fun (i : Fin n) => P i.succ)) <;> rename_i H'
        · apply isFalse
          intros Hc
          apply H'
          intros i
          apply Hc
        · apply isTrue
          intros j
          apply Fin.cases <;> assumption

  instance {n : Nat} (P : Fin n → Prop) [DecidablePred P] :
    Decidable (∀ (i : Fin n), P i) := dec_forall_fin P

  def dec_exists_fin {n : Nat} (P : Fin n → Prop) [ι : DecidablePred P] :
    Decidable (∃ (i : Fin n), P i)
  := by
    induction n
    · apply isFalse
      intros Hc
      cases Hc
      rename_i v _
      cases v
      rename_i Hc _
      cases Hc
    · rename_i n IH
      cases (ι 0) <;> rename_i H
      · cases (IH (fun (i : Fin n) => P i.succ)) <;> rename_i H'
        · apply isFalse
          have HF : ∀ (i : Fin n.succ), ¬P i := by
            intros i
            apply (@Fin.cases n (fun i => ¬P i))
            · assumption
            · intros j Hc
              apply H'
              exists j
          intros Hc
          cases Hc
          apply HF
          assumption
        · apply isTrue
          cases H'
          rename_i i _
          exists i.succ
      · apply isTrue
        exists 0

  instance {n : Nat} (P : Fin n → Prop) [DecidablePred P] :
    Decidable (∃ (i : Fin n), P i) := dec_exists_fin P

  def dec_unique_fin {n : Nat} (P : Fin n → Prop) [ι : DecidablePred P] :
    DecidablePred (unique P)
  := by
    intros i
    unfold unique
    apply inferInstance

  instance {n : Nat} (P : Fin n → Prop) [DecidablePred P] :
    DecidablePred (unique P) := dec_unique_fin P

  def exists_unique_fin {n : Nat} (P : Fin n → Prop) [DecidablePred P] :
    Decidable (∃ (i : Fin n), unique P i) := inferInstance

  instance {n : Nat} (P : Fin n → Prop) [DecidablePred P] :
    Decidable (∃ (i : Fin n), unique P i) := exists_unique_fin P-/
