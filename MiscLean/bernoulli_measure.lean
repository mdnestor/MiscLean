import Mathlib.Probability.ProductMeasure
import Mathlib.Dynamics.Ergodic.MeasurePreserving

open MeasureTheory

-- the discrete measurable space
instance (X: Type u): MeasurableSpace X := ⊤

-- given an extended nonnegateive real valued function on a set, we can define the discrete measure by
-- μ(A) = ∑_(x ∈ A) f(x)
noncomputable def discrete_measure {X: Type u} (f: X → ENNReal): @Measure X ⊤ := {
  measureOf := fun S => ∑' (x: S), f x
  empty := tsum_empty
  mono := ENNReal.tsum_mono_subtype f
  iUnion_nat := fun s _ => ENNReal.tsum_iUnion_le_tsum f s
  m_iUnion := by intros; sorry -- these should be simple?
  trim_le := by sorry
}

-- if ∑_x f(x) = 1 then the discrete measure is a probability measure
theorem discrete_measure_is_probability_measure {X: Type u} {f: X → ENNReal} (hf: ∑' x, f x = 1): IsProbabilityMeasure (discrete_measure f) := {
  measure_univ := by
    rw [←hf, ←tsum_univ]
    rfl
}

noncomputable def discrete_probability_measure (X: Type u) (f: X → ENNReal) (hf: ∑' x, f x = 1): ProbabilityMeasure X :=
  ⟨discrete_measure f, discrete_measure_is_probability_measure hf⟩

-- given two sets X and I, this forms the product discrete measurable space on I → X
noncomputable def prodiscrete_measure (X: Type u) (I: Type v): MeasurableSpace (I → X) :=
  MeasurableSpace.pi

-- the Bernoulli measure
noncomputable def BernoulliMeasure {X: Type u} {f: X → ENNReal} (hf: ∑' x, f x = 1) (I: Type v): Measure (I → X) :=
  Measure.infinitePi (hμ := fun _ => discrete_measure_is_probability_measure hf)

noncomputable def BernoulliProbabilityMeasure {X: Type u} {f: X → ENNReal} (hf: ∑' x, f x = 1) (I: Type v): ProbabilityMeasure (I → X) :=
  ⟨BernoulliMeasure hf I, MeasureTheory.Measure.instIsProbabilityMeasureForallInfinitePi (hμ := fun _ => discrete_measure_is_probability_measure hf)⟩

def shift (X: Type u) {T: Type v} [Mul T] (t0: T): (T → X) → (T → X) :=
  fun f => fun t => f (t0 * t)

-- next I want to prove this is a measure preserving transformation
theorem Bernoulli_shift_measure_preserving {X: Type u} {f: X → ENNReal} (hf: ∑' x, f x = 1) {T: Type v} [Group T] (t0: T): MeasureTheory.MeasurePreserving (shift X t0) (BernoulliMeasure hf T) (BernoulliMeasure hf T) := {
  measurable := by sorry
  map_eq := by sorry
}
