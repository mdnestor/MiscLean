-- https://en.wikipedia.org/wiki/Drinker_paradox


example {X: Type} [Nonempty X] (P: X → Prop): ∃ x, (P x → ∀ x, P x) := by
  by_cases h: ∀ x, P x
  . -- if ∀ x, P x then any x will do
    exists Classical.ofNonempty
    intro
    exact h
  . -- otherwise, if ∃ x, ¬ P x, then the conclusion holds vacuously
    simp at h
    obtain ⟨x, hx⟩ := h
    exists x
    intro
    contradiction
