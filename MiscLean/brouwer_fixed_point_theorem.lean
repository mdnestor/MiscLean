/-
A very rough sketch of the homological proof of Brouwer fixed point theorem
- If there exists a map D^n \to D^n without a fixed point, then there is a retraction of D^n onto S^(n-1).
- When you take the image under the n-th homology functor, this retraction becomes an injective homomorphism from Z to 0.
- But this is a contradiction, so f must have a fixed point.
-/

structure TopSpace where
  point: Type

axiom nBall (n: Nat): TopSpace

axiom nSphere (n: Nat): TopSpace

structure Continuous (X Y: TopSpace) where
  map: X.point → Y.point

axiom has_fixed_point {X: TopSpace} (f: Continuous X X): Prop

axiom Group: Type

structure Homomorphism (X Y: Group)

axiom injective {X Y: Group} (f: Homomorphism X Y): Prop

axiom Trivial: Group

axiom Z: Group

axiom cannot_inject_Z_into_trivial (f: Homomorphism Z Trivial): ¬ injective f

axiom homology0 (X: TopSpace) (n: Nat): Group

axiom homology1 {X Y: TopSpace} (f: Continuous X Y) (n: Nat): Homomorphism (homology0 Y n) (homology0 X n)

axiom ball_homology (n: Nat): homology0 (nBall (n + 1)) n = Trivial

axiom sphere_homology (n: Nat): homology0 (nSphere n) n = Z

axiom retraction {X Y: TopSpace} (f: Continuous X Y): Prop

axiom homology_fact {X Y: TopSpace} (f: Continuous X Y) (h: retraction f) (n: Nat): injective (homology1 f n)

/- this is the retraction from the ball to its boundary -/
axiom R {n: Nat} (f: Continuous (nBall (n+1)) (nBall (n+1))) (h: ¬ has_fixed_point f): Continuous (nBall (n+1)) (nSphere n)

axiom R_is_retraction {n: Nat} (f: Continuous (nBall (n+1)) (nBall (n+1))) (h: ¬ has_fixed_point f): retraction (R f h)

noncomputable def induced_homomorphism {n: Nat} (f: Continuous (nBall (n+1)) (nBall (n+1))) (h: ¬ has_fixed_point f): Homomorphism Z Trivial := by
  have r := R f h
  have g := homology1 r n
  rw [←ball_homology, ←sphere_homology]
  exact g

def no_fp_implies_injective {n: Nat} (f: Continuous (nBall (n+1)) (nBall (n+1))) (h: ¬ has_fixed_point f): injective (induced_homomorphism f h) := by
  have r := R f h
  have h1: retraction r := sorry /- apply R_is_retraction? -/
  have h2 := homology_fact r h1 n
  sorry /- need to show homology1 r n = induced_homomorphism f h -/

def no_fp_impossible (n: Nat) (f: Continuous (nBall (n+1)) (nBall (n+1))) (h: ¬ has_fixed_point f): False := by
  have h2 := no_fp_implies_injective f h
  apply cannot_inject_Z_into_trivial
  exact h2

axiom contradiction {P: Prop} (h: ¬P → False): P

theorem Brouwer (n: Nat) (f: Continuous (nBall (n+1)) (nBall (n+1))): has_fixed_point f := by
  exact contradiction fun hc => no_fp_impossible n f hc
