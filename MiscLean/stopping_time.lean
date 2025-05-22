-- some results about stopping times

import Mathlib.Data.Set.Basic

def StoppingTime {Ω T: Type} [LE T] (τ: Ω → T) (F: T → Set (Set Ω)): Prop :=
  ∀ t, {ω | τ ω ≤ t} ∈ F t

-- hF is F is closed under binary union
example {Ω T: Type} [LinearOrder T] {F: T → Set (Set Ω)} (hF: ∀ t, ∀ A B: Set Ω, A ∈ F t → B ∈ F t → A ∪ B ∈ F t) {σ τ: Ω → T} (hσ: StoppingTime σ F) (hτ: StoppingTime τ F): StoppingTime (min σ τ) F := by
  intro t
  simp
  apply hF
  exact hσ t
  exact hτ t

-- hF is F is closed under binary intersection
example {Ω T: Type} [LinearOrder T] {F: T → Set (Set Ω)} (hF: ∀ t, ∀ A B: Set Ω, A ∈ F t → B ∈ F t → A ∩ B ∈ F t) {σ τ: Ω → T} (hσ: StoppingTime σ F) (hτ: StoppingTime τ F): StoppingTime (max σ τ) F := by
  intro t
  simp
  apply hF
  exact hσ t
  exact hτ t

example {Ω T: Type} [LE T] {F: T → Set (Set Ω)} (hF1: ∀ t, ⊥ ∈ F t) (hF2: ∀ t, ⊤ ∈ F t) (c: T): StoppingTime (fun _ => c) F := by
  intro t
  by_cases h: c ≤ t
  simp_all
  have: {ω: Ω | c ≤ t} = ∅ := Set.subset_eq_empty (fun _ => h) rfl
  rw [this]
  exact hF1 t

/-
another important one: if F is closed under countable union
then {T < t} is Ft-measurable.
proof: {T < t} = ⋃_{n=1}^{∞} {T ≤ t - 1/n}
-/
