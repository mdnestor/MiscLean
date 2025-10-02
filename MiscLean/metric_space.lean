
structure MetricSpace where
  point: Type
  distance: point -> point -> Float
  d0: forall x: point, distance x x = 0
  d1: forall x y: point, x ≠ y -> distance x y ≠ 0
  d2: forall x y: point, distance x y = distance y x
  d3: forall x y z: point, distance x y + distance y z ≥ distance x z

def subset (T: Type): Type := T -> Prop

structure subtype {T: Type} (S: subset T) where
  element: T
  belongs: S element

def MetricSpace.sub {M: MetricSpace} (S: subset M.point): MetricSpace := {
  point := subtype S
  distance := fun x y => M.distance x.element y.element
  d0 := by intros; apply M.d0
  d1 := sorry
  d2 := by intros; apply M.d2
  d3 := by intros; simp; apply M.d3
}

def DiscreteMetric (T: Type) [DecidableEq T]: MetricSpace := {
  point := T
  distance := fun x y => if x = y then 0 else 1
  d0 := by simp
  d1 := by intro x y; simp; sorry
  d2 := by intro x y; simp; sorry
  d3 := by intro x y z; simp; sorry
}

/-
Some notions to define:
convergence
completeness
Completion of a metric space
bounded and totally bounded (precompact)
compact
isometry
continuous
homeomorphism
uniformly continuous
lipschitz maps and contractions
-/

def converges_to {M: MetricSpace} (a: Nat -> M.point) (x: M.point): Prop :=
  forall epsilon: Float, exists N: Nat, forall n: Nat, (epsilon > 0) ∧ (n ≥ N) -> M.distance (a n) x < epsilon
def converges {M: MetricSpace} (a: Nat -> M.point): Prop :=
  exists x: M.point, converges_to a x
def Cauchy {M: MetricSpace} (a: Nat -> M.point): Prop :=
  forall epsilon: Float, exists N: Nat, forall m n: Nat, (epsilon > 0) ∧ (n ≥ N) ∧ (m ≥ N) -> M.distance (a n) (a m) < epsilon
def complete (M: MetricSpace): Prop :=
  forall a: Nat -> M.point, Cauchy a -> converges a
def completion (M: MetricSpace): MetricSpace := sorry
example: forall M: MetricSpace, complete (completion M) := sorry
def bounded_by (M: MetricSpace) (r: Float): Prop :=
  forall x y: M.point, M.distance x y ≤ r
def diameter (M: MetricSpace) (r: Float): Prop :=
  (bounded_by M r) ∧ (forall s: Float, s < r -> ¬ bounded_by M s)

def distance_preserving {M1 M2: MetricSpace} (f: M1.point -> M2.point): Prop :=
  forall x y: M1.point, M1.distance x y = M2.distance (f x) (f y)

def injective {A B: Type} (f: A -> B): Prop := forall a1 a2: A, f a1 = f a2 -> a1 = a2
def surjective {A B: Type} (f: A -> B): Prop := forall b: B, exists a: A, f a = b
def bijective {A B: Type} (f: A -> B): Prop := (injective f) ∧ (surjective f)

theorem distance_preserving_implies_injective:
  forall M1 M2: MetricSpace, forall f: M1.point -> M2.point, distance_preserving f -> injective f :=
  sorry

def isometry {M1 M2: MetricSpace} (f: M1.point -> M2.point): Prop :=
  (bijective f) ∧ (distance_preserving f)
def isometric (M1 M2: MetricSpace): Prop :=
  exists f: M1.point -> M2.point, isometry f

theorem distance_preserving_and_surjective_implies_isometry:
  forall M1 M2: MetricSpace, forall f: M1.point -> M2.point, distance_preserving f ∧ surjective f -> isometry f := by
  intro _ _ _ h; rw [isometry]; apply And.intro; rw [bijective]; apply And.intro; apply distance_preserving_implies_injective; exact h.1; exact h.2; exact h.1

def continuous_v2 {M1 M2: MetricSpace} (f: M1.point -> M2.point): Prop :=
  forall a: Nat -> M1.point, forall x: M1.point, converges_to a x -> converges_to (f ∘ a) (f x)

def continuous_v3 {M1 M2: MetricSpace} (f: M1.point -> M2.point): Prop :=
  forall x: M1.point, forall epsilon: Float, exists delta: Float, forall y: M1.point, epsilon > 0 ∧ M1.distance x y < delta -> M2.distance (f x) (f y) < epsilon

example: forall M1 M2: MetricSpace, forall f: M1.point -> M2.point, (continuous_v2 f -> continuous_v3 f) ∧ (continuous_v3 f -> continuous_v2 f) := sorry

/- they are equivalent so i will just pick one -/
def continuous {M1 M2: MetricSpace} (f: M1.point -> M2.point): Prop := continuous_v2 f

axiom inverse {A B: Type} (f: A -> B) (h: bijective f): B -> A
axiom left_inverse_id (A B: Type) (f: A -> B) (h: bijective f): forall a: A, (inverse f h) (f a) = a
axiom right_inverse_id (A B: Type) (f: A -> B) (h: bijective f): forall b: B, f ((inverse f h) b) = b

def homeomorphism {M1 M2: MetricSpace} (f: M1.point -> M2.point): Prop :=
  exists h: bijective f, continuous f ∧ continuous (inverse f h)
def homeomorphic (M1 M2: MetricSpace): Prop :=
  exists f: M1.point -> M2.point, homeomorphism f
