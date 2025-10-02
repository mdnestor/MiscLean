/-

This file shows a Borel measure is strictly positive iff. it has this property that the complement of every neglible set is dense.

Proof:
- If m is strictly positive and m(E) = 0, suppose by contradiction E^c is not dense.
Then there exists open U contained in E, so that m(E) >= m(U) > 0, contradiction.
- If m has the negligible dense complement property, and U is any open set, then U^c is not dense, so by contrapositive of assumption then m(U) > 0.

-/

import Mathlib.MeasureTheory.Constructions.BorelSpace.Basic

open MeasureTheory

-- throughout X is equipped with a topology
variable {X: Type u} [TopologicalSpace X]

instance: MeasurableSpace X :=
  borel X

def negligible_dense_compl (m: Measure X): Prop :=
  ∀ E, MeasurableSet E → m E = 0 → Dense Eᶜ

def strictly_positive (m: Measure X): Prop :=
  ∀ U, IsOpen U → U.Nonempty → m U ≠ 0

theorem negligible_dense_compl_iff (m: Measure X): negligible_dense_compl m ↔ strictly_positive m := by
  apply Iff.intro
  . intro h U U_open U_nonempty
    contrapose h
    simp [negligible_dense_compl]
    exists U
    repeat' constructor
    . exact U_open
    . exact Function.notMem_support.mp h
    . simp [dense_iff_inter_open]
      exists U
      repeat' (apply And.intro)
      . exact U_open
      . exact U_nonempty
      . simp
  . intro h E _ E_negl
    apply by_contradiction
    intro h1
    simp [dense_iff_inter_open] at h1
    obtain ⟨U, U_open, U_nonempty, U_inter_E_compl_nonempty⟩ := h1
    have m_U_pos := h U U_open U_nonempty
    have U_subset_E: U ⊆ E := by
      intro x x_in_U
      apply by_contradiction
      intro x_notin_E
      have x_in_U_inter_E_compl: x ∈ U ∩ Eᶜ := Set.mem_inter x_in_U x_notin_E
      have: U ∩ Eᶜ = ∅ := Set.not_nonempty_iff_eq_empty.mp U_inter_E_compl_nonempty
      rw [this] at x_in_U_inter_E_compl
      contradiction
    have: m E > 0 := calc
      m E ≥ m U := by exact OuterMeasureClass.measure_mono m U_subset_E
        _ > 0   := measure_pos_of_superset (by rfl) m_U_pos
    have: m E ≠ 0 := Ne.symm (ne_of_lt this)
    contradiction

-- corollary
example {X: Type u} {Y: Type v} [TopologicalSpace X] [TopologicalSpace Y] [T2Space Y] {f g: X → Y} {hf: Continuous f} {hg: Continuous g} {D: Set X} {hD0: MeasurableSet D} {hD1: ∀ x ∈ D, f x = g x} {m: Measure X} {hm: strictly_positive m} {hD2: m Dᶜ = 0}: f = g := by
  have: Dense D := by
    rw [←compl_compl D]
    apply (negligible_dense_compl_iff m).mpr hm
    exact MeasurableSet.compl_iff.mpr hD0
    exact hD2
  exact Continuous.ext_on this hf hg hD1
