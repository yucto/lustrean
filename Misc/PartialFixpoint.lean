open Lean Order

universe u v
variable {ε σ α ρ ω} {m : Type _ → Type _}

noncomputable instance [Nonempty α] : CCPO (Id α) := inferInstanceAs (CCPO (FlatOrder Classical.ofNonempty))
noncomputable instance [Nonempty ε] : CCPO (EStateM ε σ α) :=
  inferInstanceAs (CCPO ((s : σ) → FlatOrder (.error Classical.ofNonempty (Classical.choice ⟨s⟩))))

noncomputable instance [Nonempty ε] : CCPO (EIO ε α) := inferInstanceAs (CCPO (EStateM _ _ _))

noncomputable instance [∀ α, PartialOrder (m α)] : PartialOrder (ReaderT ρ m α) := inferInstanceAs (PartialOrder (_ → _))
noncomputable instance [∀ α, PartialOrder (m α)] : PartialOrder (StateT ρ m α) := inferInstanceAs (PartialOrder (_ → _))
noncomputable instance [∀ α, PartialOrder (m α)] : PartialOrder (StateRefT' ω σ m α) := inferInstanceAs (PartialOrder (_ → _))
noncomputable instance [∀ α, CCPO (m α)] : CCPO (ReaderT ρ m α) := inferInstanceAs (CCPO (_ → _))
noncomputable instance [∀ α, CCPO (m α)] : CCPO (StateT ρ m α) := inferInstanceAs (CCPO (_ → _))
noncomputable instance [∀ α, CCPO (m α)] : CCPO (StateRefT' ω σ m α) := inferInstanceAs (CCPO (_ → _))

instance [Nonempty ε] : MonoBind (EStateM ε σ) where
  bind_mono_left {_ _ a₁ a₂ f} h s := by
    specialize h s
    simp only [bind, EStateM.bind]
    generalize a₁ s = a₁ at h
    generalize a₂ s = a₂ at h
    cases h
    · exact .bot
    · exact .refl
  bind_mono_right {_ _ a f₁ f₂} h s := by
    simp only [bind, EStateM.bind]
    split
    · apply h
    · exact .refl

instance [Monad m] [∀ α, PartialOrder (m α)] [MonoBind m] : MonoBind (ReaderT ρ m) where
  bind_mono_left h s := MonoBind.bind_mono_left (h s)
  bind_mono_right h s := MonoBind.bind_mono_right (fun x => h x s)

instance [Monad m] [∀ α, PartialOrder (m α)] [MonoBind m] : MonoBind (StateT ρ m) where
  bind_mono_left h s := MonoBind.bind_mono_left (h s)
  bind_mono_right h _ := MonoBind.bind_mono_right (fun x => h x.1 x.2)

instance [Monad m] [∀ α, PartialOrder (m α)] [MonoBind m] : MonoBind (StateRefT' ω σ m) :=
  inferInstanceAs (MonoBind (ReaderT _ _))
