-- point set topology

def subset (X: Type): Type := X -> Prop
def empty (X: Type): subset X := fun _ => False
def whole (X: Type): subset X := fun _ => True
def cup {X: Type} (A B: subset X): subset X := fun x => A x ∨ B x
def cap {X: Type} (A B: subset X): subset X := fun x => A x ∧ B x
def subset_of {X: Type} (A B: subset X): Prop := forall x: X, A x -> B x
def image {X Y: Type} (f: X -> Y) (A: subset X): subset Y := fun y => exists x: X, A x ∧ f x = y
def preimage {X Y: Type} (f: X -> Y) (B: subset Y): subset X := fun x => B (f x)

-- neighborhood axiomatization of topological spaces
structure TopologicalSpaceV0 where
  point: Type
  neighborhoods: point -> subset (subset point)
  t1: forall x: point, forall S: subset point, (neighborhoods x) S -> S x
  t2: forall x: point, forall S1 S2: subset point, (neighborhoods x) S1 ∧ subset_of S1 S2 -> (neighborhoods x) S2
  t3: forall x: point, forall S1 S2: subset point, (neighborhoods x) S1 ∧ (neighborhoods x) S2 -> (neighborhoods x) (cap S1 S2)
  t4: forall x: point, forall S1: subset point, exists S2: subset point, forall y: point, S2 x ∧ S2 y -> (neighborhoods x S2) ∧ (neighborhoods y S1)

def is_open {T: TopologicalSpaceV0} (S: subset T.point): Prop :=
  forall x: T.point, S x -> T.neighborhoods x S

structure TopologicalSpace_old where
  point: Type
  openset: subset (subset point)
  t1: openset (empty point)
  t2: openset (whole point)
  t3: forall A B: subset point, openset A ∧ openset B -> openset (cap A B)
  t4: forall I: Type, forall A: I -> subset point, (forall i: I, openset (A i)) -> openset (bigcup_old A)

def bigcup {X: Type} (S: subset (subset X)): subset X := fun x => exists A: subset X, S A ∧ A x
def bigcap {X: Type} (S: subset (subset X)): subset X := fun x => forall A: subset X, S A ∧ A x
def finite {X: Type} (A: subset X): Prop := exists L: List X, forall x: X, A x -> x ∈ L

structure TopologicalSpace where
  point: Type
  openset: subset (subset point)
  t1: openset (empty point)
  t2: openset (whole point)
  t3: forall A B: subset point, openset A ∧ openset B -> openset (cap A B)
  t4: forall S: subset (subset point), (forall U: subset point, S U -> openset U) -> openset (bigcup S)

def open_cover {X: TopologicalSpace} (S: subset (subset X.point)): Prop :=
  (forall A: subset X.point, S A -> X.openset A) ∧ (bigcup S = whole X.point)

def compact (X: TopologicalSpace): Prop :=
  forall S: subset (subset X.point), exists F: subset (subset X.point), open_cover S -> (subset_of F S) ∧ (open_cover F) ∧ (finite F)

def continuous {T1 T2: TopologicalSpace} (f: T1.point -> T2.point): Prop :=
  forall B: subset T2.point, T2.openset B -> T1.openset (preimage f B)

def convert (T: TopologicalSpaceV0): TopologicalSpace := {
  point := T.point
  openset := fun S => forall x: T.point, S x -> T.neighborhoods x S
  t1 := sorry
  t2 := sorry
  t3 := sorry
  t4 := sorry
}

def deconvert (T: TopologicalSpace): TopologicalSpaceV0 := {
  point := T.point
  neighborhoods := fun x S => exists U: subset T.point, (T.openset U) ∧ (subset_of S U) ∧ (U x)
  t1 := sorry
  t2 := sorry
  t3 := sorry
  t4 := sorry
}
