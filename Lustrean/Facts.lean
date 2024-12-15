import Aesop

namespace Int
  theorem min_assoc : ∀ (n m o : Int),
    min (min n m) o = min n (min m o) :=
  by
    intro n m o
    repeat rw [Int.min_def]
    repeat' split
    all_goals omega

  theorem max_assoc : ∀ (n m o : Int),
    max (max n m) o = max n (max m o) :=
  by
    intro n m o
    repeat rw [Int.max_def]
    repeat' split
    all_goals omega

  theorem min_max_absorb : ∀ (n m : Int),
    min n (max n m) = n :=
  by
    intro n m
    apply Int.min_eq_left
    apply Int.le_max_left

  theorem max_min_absorb : ∀ (n m : Int),
    max n (min n m) = n :=
  by
    intro n m
    apply Int.max_eq_left
    apply Int.min_le_left

  theorem min_alternative : ∀ (n m : Int),
    min n m = n ∨ min n m = m :=
  by
    intros n m
    rw [Int.min_def]
    split
    · left <;> rfl
    · right <;> rfl

  theorem max_alternative : ∀ (n m : Int),
    max n m = n ∨ max n m = m :=
  by
    intros n m
    rw [Int.max_def]
    split
    · right <;> rfl
    · left <;> rfl
end Int

namespace Decidable
  def decide_and : ∀ (p q : Prop),
    Decidable p -> Decidable q -> Decidable (p ∧ q) :=
  by
    intros p q ι ι'
    cases ι <;> cases ι' <;>
    rename_i h h' <;>
    (try apply Decidable.isTrue <;> constructor <;> assumption) <;>
    apply Decidable.isFalse <;>
    intros H <;>
    cases H <;>
    solve | apply h <;> assumption | apply h' <;> assumption


  def decidableExistsFin {n : Nat} (P : Fin n → Prop) [ι : DecidablePred P] :
    Decidable (∃ (i : Fin n), P i)
  := by
    induction n
    case zero =>
      apply isFalse
      intro ⟨⟨_, Hi⟩, _⟩
      cases Hi
    case succ n IHn =>
      let P' := fun (i : Fin n) => P i.succ
      --have ι' : DecidablePred P' := fun (i : Fin n) => ι i.succ
      by_cases P 0
      case pos H0 =>
        apply isTrue
        exists 0
      case neg H0 =>
        by_cases ∃ i, P' i
        case pos Hn =>
          apply isTrue
          let ⟨i, Hi⟩ := Hn
          exists i.succ
        case neg Hn =>
          apply isFalse
          rw [Fin.exists_fin_succ]
          intros Hc
          cases Hc <;> [
            apply H0 ;
            apply Hn
          ] <;> assumption

  instance {n : Nat} (P : Fin n → Prop) [DecidablePred P] :
    Decidable (∃ (i : Fin n), P i)
  := decidableExistsFin P
end Decidable

namespace Array
  def All {α : Type} (P : α → Prop) (as : Array α) : Prop :=
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
      have Hi : (as.extract 1 as.size).size = n := by simp [Heq]
      (Heq ▸ f) (Hi ▸ i).succ
    )
    init
    (by simp [Heq])
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
    · have ⟨Ha, Hl⟩ := H
      intros a' Ha'
      cases Ha' with
      | head => assumption
      | tail =>
        apply Hl
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
