
import Mathlib

open MeasureTheory

def limit {X: Type u} [TopologicalSpace X] (x: Nat → X) (x0: X): Prop :=
  Filter.Tendsto x ⊤ (nhds x0)

def limsup {X: Type u} (A: Nat → Set X): Set X :=
  Set.iInter fun n => Set.iUnion fun m => A (m + n)

theorem continuity_from_above {X: Type u} [MeasurableSpace X] (μ: Measure X) {A: Nat → Set X} (h1: ∀ n, MeasurableSet (A n)) (h2: ∀ n: Nat, A n ⊇ A (n + 1)): limit (fun n => μ (A n)) (μ (Set.iInter A)) := by
  sorry

theorem Borel_Cantelli {X: Type u} [MeasurableSpace X] {μ: Measure X} {A: Nat → Set X} (h1: ∀ n, MeasurableSet (A n)) (h2: ∑' n, μ (A n) ≠ ⊤): μ (limsup A) = 0 := by
  
  let B := fun n => Set.iUnion fun m => A (m + n)
  
  have hB1: ∀ n, MeasurableSet (B n) := by
    intro i
    apply MeasurableSpace.measurableSet_iUnion
    intro j
    exact h1 (j + i)
  
  have hB2: ∀ n, B n ⊇ B (n + 1) := by
    intro n _ hx
    simp_all [B]
    obtain ⟨i, hi⟩ := hx
    exists i + 1
    rw [Nat.add_assoc, Nat.add_comm 1 n]
    exact hi
  
  have lim_μBn_eq_μlimsupBn := continuity_from_above μ hB1 hB2

  have: limsup A = Set.iInter B := by
    ext x
    constructor
    . intro hx
      simp_all [limsup]
      intro n
      obtain ⟨i, hi⟩ := hx n
      simp [B]
      exists i
    . intro hx
      simp_all [limsup]
      intro n
      obtain ⟨i, hi⟩ := hx n
      simp_all [B]
  rw [this]

  have lim_μBn_eq_zero: limit (fun n => μ (B n)) 0 := by
    sorry
  
  exact tendsto_nhds_unique lim_μBn_eq_μlimsupBn lim_μBn_eq_zero
