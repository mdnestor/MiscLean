
/-

This file shows two definitions of sigma-algebra are equivalent.

-/

import Mathlib.Data.Set.Basic
import Mathlib.Data.Set.Countable

abbrev Set.empty {X: Type u}: Set X :=
  ∅


-- First definition: via sequences and indexed unions
structure SigmaAlgebra1 {X: Type u} (F: Set (Set X)) where
  compl: ∀ A, A ∈ F → Aᶜ ∈ F
  union: ∀ a: ℕ → Set X, (∀ i, a i ∈ F) → Set.iUnion a ∈ F
  univ: ⊤ ∈ F -- ⊤ denotes the universal set, F itself

theorem SigmaAlgebra1.empty_mem {X: Type u} {F: Set (Set X)} (h: SigmaAlgebra1 F): ∅ ∈ F := by
  have := h.compl ⊤ h.univ
  simp_all

-- Second definition: via set unions.
-- Note that we don't need to manually specify ⊤ ∈ F
structure SigmaAlgebra2 {X: Type u} (F: Set (Set X)) where
  compl: ∀ A, A ∈ F → Aᶜ ∈ F
  union: ∀ C, C ⊆ F → Countable C → Set.sUnion C ∈ F

theorem SigmaAlgebra2.empty_mem {X: Type u} {F: Set (Set X)} (h: SigmaAlgebra2 F): ∅ ∈ F := by
  let C := @Set.empty (Set X)
  rw [←Set.sUnion_empty]
  apply h.union C
  apply Set.empty_subset
  exact Subsingleton.to_countable

theorem SigmaAlgebra2.univ_mem {X: Type u} {F: Set (Set X)} (h: SigmaAlgebra2 F): ⊤ ∈ F := by
  have: ⊤ = (∅ᶜ: Set X) := by simp
  rw [this]
  apply h.compl
  exact empty_mem h

-- Main theorem: the two definitions are equivalent.
example {X: Type u} (F: Set (Set X)): SigmaAlgebra1 F ↔ SigmaAlgebra2 F := by
  constructor
  . intro h
    constructor
    . exact h.compl
    . intro C h1 h2
      by_cases h3: Set.Nonempty C
      . obtain ⟨a, h4⟩ := (Set.countable_iff_exists_surjective h3).mp h2
        -- helper lemma could probably be cleaned up..
        have: ⋃₀ C = ⋃ n, (a n) := by
          ext
          constructor
          . intro hx
            obtain ⟨A, hA⟩ := hx
            obtain ⟨i, hi⟩ := h4 ⟨A, hA.1⟩
            simp
            exists i
            rw [hi]
            exact hA.2
          . intro hx
            simp_all
            obtain ⟨i, hi⟩ := hx
            exists a i
            constructor
            . exact (a i).prop
            . exact hi
        rw [this]
        apply h.union fun n => (a n).val
        intro i
        exact h1 (a i).prop
      . simp [Set.not_nonempty_iff_eq_empty.mp h3]
        exact SigmaAlgebra1.empty_mem h
  . intro h
    constructor
    . exact h.compl
    . intro _ h1
      apply h.union
      exact Set.range_subset_iff.mpr h1
      apply Set.countable_range
    . exact SigmaAlgebra2.univ_mem h
