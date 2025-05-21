/-

If T and S are stopping times then so is S ∧ T

-/

import Mathlib.Data.Set.Basic

def StoppingTime {Ω T: Type} [LE T] (τ: Ω → T) (F: T → Set (Set Ω)): Prop :=
  ∀ t: T, {ω | τ ω ≤ t} ∈ F t

example {X: Type} [LinearOrder X] (x y: X): min x y ≤ x := by
  exact min_le_left x y

example {Ω T: Type} [LinearOrder T] {F: T → Set (Set Ω)} (hF: ∀ t, ∀ A B: Set Ω, A ∈ F t → B ∈ F t → A ∪ B ∈ F t) {σ τ: Ω → T} (hσ: StoppingTime σ F) (hτ: StoppingTime τ F): StoppingTime (min σ τ) F := by
  intro t
  simp
  apply hF
  exact hσ t
  exact hτ t
