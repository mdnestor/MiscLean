-- some results about stopping times

import Mathlib.Data.Set.Basic
import Mathlib.Data.Real.Basic

def StoppingTime {Ω T: Type} [LE T] (τ: Ω → T) (F: T → Set (Set Ω)): Prop :=
  ∀ t, {ω | τ ω ≤ t} ∈ F t

-- is σ, τ are stopping times then so it min σ τ
-- hF is F is closed under binary union
example {Ω T: Type} [LinearOrder T] {F: T → Set (Set Ω)} (hF: ∀ t, ∀ A B: Set Ω, A ∈ F t → B ∈ F t → A ∪ B ∈ F t) {σ τ: Ω → T} (hσ: StoppingTime σ F) (hτ: StoppingTime τ F): StoppingTime (min σ τ) F := by
  intro t
  simp
  apply hF
  exact hσ t
  exact hτ t


-- is σ, τ are stopping times then so it max σ τ
-- hF is F is closed under binary intersection
example {Ω T: Type} [LinearOrder T] {F: T → Set (Set Ω)} (hF: ∀ t, ∀ A B: Set Ω, A ∈ F t → B ∈ F t → A ∩ B ∈ F t) {σ τ: Ω → T} (hσ: StoppingTime σ F) (hτ: StoppingTime τ F): StoppingTime (max σ τ) F := by
  intro t
  simp
  apply hF
  exact hσ t
  exact hτ t

-- the constant function is a stopping time (assuming ∅ ∈ F t and Ω ∈ F t for all t.)
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
we will just assume T is real numbers
-/

theorem interval_union {X: Type} {f: X → ℝ} (a: ℝ): {x | f x < a} = Set.iUnion fun n: Nat => {x | f x ≤ a - 1/n} := by
  sorry

def OptionalTime {Ω T: Type} [LT T] (τ: Ω → T) (F: T → Set (Set Ω)): Prop :=
  ∀ t, {ω | τ ω < t} ∈ F t

-- every stopping time is an optional time
-- need to assume F is monotone wrt. t, and each F t is closed under countable union
example {Ω: Type} {F: ℝ → Set (Set Ω)} {hF1: ∀ t, ∀ A: Nat → Set Ω, (∀ n, A n ∈ F t) → Set.iUnion A ∈ F t} {hF2: ∀ s t, s ≤ t → F s ⊆ F t} {τ: Ω → Real} (hτ: StoppingTime τ F): OptionalTime τ F := by
  intro t
  rw [interval_union t]
  apply hF1
  intro n
  apply hF2 (t - 1/n) t
  aesop
  apply hτ
