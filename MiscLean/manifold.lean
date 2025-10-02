
/- a manifold in which a neighborhood of evrey point is homeomorphic to R^n -/
/- https://en.wikipedia.org/wiki/Manifold -/

def subset (X: Type): Type := X -> Prop

structure subtype {X: Type} (S: subset X) where
  x: X
  ok: S x

structure TopologicalSpace where
  element: Type
  openset: subset (subset element)

def EuclideanSpace (n: Nat): TopologicalSpace :=
  sorry

def Subspace {X: TopologicalSpace} (S: subset X.element): TopologicalSpace := {
  element := subtype S
  openset := sorry
}

def injective (f: X -> Y): Prop :=
  forall x1 x2: X, f x1 = f x2 -> x1 = x2

def surjective (f: X -> Y): Prop :=
  forall y: Y, exists x: X, f x = y

def bijective (f: X -> Y): Prop :=
  injective f ∧ surjective f

def inverse (f: X -> Y) (h: bijective f): Y -> X :=
  sorry

def left_inverse_id (f: X -> Y) (h: bijective f): forall x: X, (inverse f h) (f x) = x :=
  sorry

def right_inverse_id (f: X -> Y) (h: bijective f): forall x: X, f ((inverse f h) y) = y :=
  sorry

def image (f: X -> Y) (S: subset X): subset Y :=
  fun y => exists x: X, S x ∧ f x = y

def preimage (f: X -> Y) (S: subset Y): subset X :=
  fun x => S (f x)

def continuous {X Y: TopologicalSpace} (f: X.element -> Y.element): Prop :=
  forall S: subset Y.element, Y.openset S -> X.openset (preimage f S)

def homeomorphism {X Y: TopologicalSpace} (f: X.element -> Y.element): Prop :=
  exists h: bijective f, continuous f ∧ continuous (inverse f h)

def homeomorphic (X Y: TopologicalSpace): Prop :=
  exists f: X.element -> Y.element, homeomorphism f

def Manifold (X: TopologicalSpace): Prop :=
  forall x: X.element, exists n: Nat, exists S: subset X.element, S x ∧ (homeomorphic (Subspace S) (EuclideanSpace n))

def PureManifold (X: TopologicalSpace): Prop :=
  exists n: Nat, forall x: X.element, exists S: subset X.element, S x ∧ (homeomorphic (Subspace S) (EuclideanSpace n))

def nManifold (X: TopologicalSpace) (n: Nat): Prop :=
  forall x: X.element, exists S: subset X.element, S x ∧ (homeomorphic (Subspace S) (EuclideanSpace n))

theorem PureManifoldIsManifold: forall X: TopologicalSpace, PureManifold X -> Manifold X := sorry
