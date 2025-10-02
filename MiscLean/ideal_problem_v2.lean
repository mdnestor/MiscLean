-- challenge problem

def subset (X: Type): Type := X -> Prop
def subset_of {X: Type} (S1 S2: subset X): Prop := forall x: X, S1 x -> S2 x
def const {X Y: Type} (y: Y): X -> Y := fun _ => y

structure TopSpace (X: Type) where
  openset: subset (subset X)

def closed {A: TopSpace X} (S: subset X): Prop :=
  ¬ A.openset S

structure Ring (X: Type) where
  add: X -> X -> X
  mul: X -> X -> X
  zero: X
  neg: X -> X

def locus {X Y: Type} (A: Ring Y) (f: X -> Y): subset X :=
  fun x => ¬ f x = A.zero

def set_locus {X Y: Type} (A: Ring Y) (S: subset (X -> Y)): subset X :=
  fun x => forall f: X -> Y, S f -> ¬ f x = A.zero

structure TopRing (X: Type) where
  openset: subset (subset X)
  add: X -> X -> X
  mul: X -> X -> X
  zero: X

example (A: TopRing X): TopSpace X := {
  openset := A.openset
}
example (A: TopRing X): Ring X := {
  add := A.add, mul := A.mul, zero := A.zero
}

/- need to define an ideal -/
structure Group (X: Type) where
  op: X -> X -> X
  id: X
  inv: X -> X

def AdditiveGroup (A: Ring X): Group X := {
  op := A.add
  id := A.zero
  inv := A.neg
}

def subgroup1 (A: Group X) (S: subset X): Prop := S A.id
def subgroup2 (A: Group X) (S: subset X): Prop := forall x y: X, S x ∧ S y -> S (A.op x y)
def subgroup3 (A: Group X) (S: subset X): Prop := forall x: X, S x -> S (A.inv x)
def subgroup (A: Group X) (S: subset X): Prop := subgroup1 A S ∧ subgroup2 A S ∧ subgroup3 A S

def absorbing (A: Ring X) (S: subset X): Prop := forall x y: X, S x -> S (A.mul x y)

def ideal (A: Ring X) (S: subset X): Prop := subgroup (AdditiveGroup A) S ∧ absorbing A S

def FunRing (X: Type) (A: Ring Y): Ring (X -> Y) := {
  add := fun f g x => A.add (f x) (g x)
  mul := fun f g x => A.mul (f x) (g x)
  zero := const A.zero
  neg := fun f => fun x => A.neg (f x)
}

def TopFunRing (X: Type) (A: Ring Y): TopRing (X -> Y) := {
  openset := sorry /- is there a canonical way to put a topology? probably not -/
  add := fun f g x => A.add (f x) (g x)
  mul := fun f g x => A.mul (f x) (g x)
  zero := const A.zero
}

def coupling_property {X Y: Type} {A: Ring Y}: forall S: subset (X -> Y), forall f: X -> Y, ¬ (TopFunRing X A).openset S ∧ ideal (FunRing X A) S ∧ subset_of (set_locus A S) (locus A f) -> S f := sorry
