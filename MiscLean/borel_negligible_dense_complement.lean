-- a Borel measure is strictly positive iff. it has this property that the complement of every neglible set is dense.

import Mathlib.MeasureTheory.Constructions.BorelSpace.Basic

open MeasureTheory

variable {X: Type u} [TopologicalSpace X]

instance: MeasurableSpace X :=
  borel X

def negligible_dense_compl (m: Measure X): Prop :=
  ∀ E, MeasurableSet E → m E = 0 → Dense Eᶜ

def strictly_positive (m: Measure X): Prop :=
  ∀ U, IsOpen U → Nonempty U → m U ≠ 0

example (m: Measure X): negligible_dense_compl m ↔ strictly_positive m := by
  constructor
  . intro h U hU1 hU2
    have hU3 := h U (MeasurableSpace.measurableSet_generateFrom hU1)
    have: ¬Dense Uᶜ := by
      simp [dense_iff_inter_open]
      exists U
      constructor
      exact hU1
      constructor
      exact nonempty_subtype.mp hU2
      simp
    exact fun a => this (hU3 a)
  . intro h E hE1 hE2
    apply by_contradiction
    intro h1
    simp [dense_iff_inter_open] at h1
    obtain ⟨U, hU1, hU2, hU3⟩ := h1
    have := h U hU1 (by exact Set.Nonempty.to_subtype hU2)
    have: U ⊆ E := by
      intro x hx
      apply by_contradiction
      intro hx2
      have hx3: x ∈ U ∩ Eᶜ := Set.mem_inter hx hx2
      have: (U ∩ Eᶜ) = ∅ := by exact Set.not_nonempty_iff_eq_empty.mp hU3
      rw [this] at hx3
      exact hx3
    have: m E > 0 :=
      calc
        m E ≥ m U := by exact OuterMeasureClass.measure_mono m (this)
          _ > 0   := measure_pos_of_superset (fun ⦃a⦄ a => a) (h U hU1 (Set.Nonempty.to_subtype hU2))
    have: m E ≠ 0 := Ne.symm (ne_of_lt this)
    exact this hE2
