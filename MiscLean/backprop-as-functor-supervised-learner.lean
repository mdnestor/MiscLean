/- https://arxiv.org/pdf/1711.10455.pdf -/

/- Definition II.1 -/
structure Learner (A B: Type) where
  param: Type
  implement: param -> A -> B
  update: param -> A -> B -> param
  request: param -> A -> B -> A

def Learner.equiv (L1 L2: Learner A B): Prop :=
  exists f: L1.param -> L2.param,
  forall p: L1.param,
  forall a: A,
  forall b: B,
  L2.implement (f p) a = L1.implement p a ∧
  L2.update (f p) a b = f (L1.update p a b) ∧
  L2.request (f p) a b = L1.request p a b

def Learner.id {A: Type}: Learner A A := {
  param := Unit,
  implement := by
    intro _ a
    exact a
  update := by
    intros
    exact ()
  request := by
    intro _ _ a
    exact a
}

def Learner.compose (L1: Learner A B) (L2: Learner B C): Learner A C := {
  param := L1.param × L2.param,
  implement := by
    intro (p1, p2) a
    exact L2.implement p2 (L1.implement p1 a)
  update := by
    intro (p1, p2) a c
    exact (
      L1.update p1 a (L2.request p2 (L1.implement p1 a) c),
      L2.update p2 (L1.implement p1 a) c
    )
  request := by
    intro (p1, p2) a c
    exact L1.request p1 a (L2.request p2 (L1.implement p1 a) c)
}

def Learner.product (L1: Learner A B) (L2: Learner C D): Learner (A × C) (B × D) := {
  param := L1.param × L2.param,
  implement := by
    intro (p1, p2) (a, c)
    exact (L1.implement p1 a, L2.implement p2 c)
  update := by
    intro (p1, p2) (a, c) (b, d)
    exact (L1.update p1 a b, L2.update p2 c d)
  request := by
    intro (p1, p2) (a, c) (b, d)
    exact (L1.request p1 a b, L2.request p2 c d)
}

def Learner.braid {A B: Type}: Learner (A × B) (B × A) := {
  param := Unit,
  implement := by
    intro _ (a, b)
    exact (b, a)
  update := by
    intros
    exact ()
  request := by
    intro _ _ (b, a)
    exact (a, b)
}

/- Proposition 2.4 -/

structure SymmMonCat where
  obj: Type u
  hom: obj -> obj -> Type v
axiom Set: Type
def Learn: SymmMonCat := {
  obj := Type
  hom := fun x y => Learner x y  
}
/- Definition 3.1 -/

structure StrictSymmMonCat where

axiom Para: StrictSymmMonCat

/- Theorem 3.2 -/

axiom R: Type

structure StrongSymmetricMonoidalFunctor (X: StrictSymmMonCat) (Y: SymmMonCat) where

def condition (f: Float -> Float -> Float): Prop := sorry

def ParaToLearn (eps: Float) (e: Float -> Float -> Float) (h1: eps > 0) (h2: condition e): StrongSymmetricMonoidalFunctor Para Learn := sorry

def faithful (F: StrongSymmetricMonoidalFunctor X Y): Prop := sorry

def injective_on_objects (F: StrongSymmetricMonoidalFunctor X Y): Prop := sorry

example (eps: Float) (e: Float -> Float -> Float) (h1: eps > 0) (h2: condition e): faithful (ParaToLearn eps e h1 h2) := sorry

example (eps: Float) (e: Float -> Float -> Float) (h1: eps > 0) (h2: condition e): injective_on_objects (ParaToLearn eps e h1 h2) := sorry

/- Definition 4.1 -/

structure Category where
  obj: Type
  hom: obj -> obj -> Type

structure NeuralNetwork (m n: Nat) where

def NNet: Category := {
  obj := Nat
  hom := fun m n => NeuralNetwork m n
}

def differentiable (f: Float -> Float): Prop := sorry

structure functor (C D: Category) where

def Forget1 (C: StrictSymmMonCat): Category := sorry

def implement (sigma: Float -> Float) (h: differentiable sigma): functor NNet (Forget1 Para) := sorry

def Forget2 (C: SymmMonCat): Category := sorry

def Forget3 (F: StrongSymmetricMonoidalFunctor X Y): functor (Forget1 X) (Forget2 Y) := sorry

def compose (F: functor C1 C2) (G: functor C2 C3): functor C1 C3 := sorry

example (eps: Float) (e: Float -> Float -> Float) (sigma: Float -> Float) (h1: eps > 0) (h2: condition e) (h3: differentiable sigma):
  functor NNet (Forget2 Learn) :=
  compose (implement sigma h3) (Forget3 (ParaToLearn eps e h1 h2))

/- todo: proposition 5.1 -/
