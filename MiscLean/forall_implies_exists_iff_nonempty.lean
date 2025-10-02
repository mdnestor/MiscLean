
theorem forall_implies_exists_iff_nonempty (P: X → Prop): ((∀ x, P x) → ∃ x, P x) ↔ Nonempty X := by
  constructor
  . intro h0
    constructor
    by_cases h1: ∀ x, P x
    . exact Classical.choose (h0 h1)
    . simp_all
      exact Classical.choose h1
  . intro _ h1
    exists Classical.ofNonempty
    apply h1
