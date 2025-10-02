/- small category -/
structure Category where
  obj: Type
  hom: obj → obj → Type
  id (a: obj): hom a a
  comp (f: hom a b) (g: hom b c): hom a c
  id_left: ∀ a b: obj, ∀ f: hom a b, f = comp (id a) f
  id_right: ∀ a b: obj, ∀ f: hom a b, f = comp f (id b)
  assoc: ∀ a b c d: obj, ∀ f: hom a b, ∀ g: hom b c, ∀ h: hom c d, comp f (comp g h) = comp (comp f g) h

structure functor (C D: Category) where
  func0: C.obj → D.obj
  func1: C.hom x y → D.hom (func0 x) (func0 y)
  id_preserving (x: C.obj):
    func1 (C.id x) = D.id (func0 x)
  comp_preserving (f: C.hom x y) (g: C.hom y z):
    func1 (C.comp f g) = D.comp (func1 f) (func1 g)

structure NaturalTransformation (F G: functor C D) where
  component (x: C.obj): D.hom (F.func0 x) (G.func0 x)
  ok (x y: C.obj) (f: C.hom x y):
    D.comp (F.func1 f) (component y) = D.comp (component x) (G.func1 f)

def isomorphism {C: Category} {x y: C.obj} (f: C.hom x y): Prop :=
  ∃ g: C.hom y x, (C.comp f g = C.id x) ∧ (C.comp g f = C.id y)

def natural_isomorphism {C D: Category} {F G: functor C D} (eta: NaturalTransformation F G): Prop :=
  ∀ x: C.obj, isomorphism (eta.component x)

/- some basics -/

def monomorphism {C: Category} {x y: C.obj} (f: C.hom x y): Prop :=
  ∀ z: C.obj, ∀ g1 g2: C.hom z x, C.comp g1 f = C.comp g2 f → g1 = g2

def epimorphism {C: Category} {x y: C.obj} (f: C.hom x y): Prop :=
  ∀ z: C.obj, ∀ g1 g2: C.hom y z, C.comp f g1 = C.comp f g2 → g1 = g2

def bimorphism {C: Category} {x y: C.obj} (f: C.hom x y): Prop :=
  (monomorphism f) ∧ (epimorphism f)

/- section was taken :( -/
def section2 {C: Category} {x y: C.obj} (f: C.hom x y): Prop :=
  ∃ g: C.hom y x, C.comp f g = C.id x

def retraction {C: Category} {x y: C.obj} (f: C.hom x y): Prop :=
  ∃ g: C.hom y x, C.comp g f = C.id y

def isomorphism2 {C: Category} {x y: C.obj} (f: C.hom x y): Prop :=
  ∃ g: C.hom y x, (C.comp f g = C.id x) ∧ (C.comp g f = C.id y)

def endomorphism {C: Category} {x y: C.obj} (f: C.hom x y): Prop :=
  x = y

def automorphism {C: Category} {x y: C.obj} (f: C.hom x y): Prop :=
  (endomorphism f) ∧ (isomorphism2 f)

example {C: Category} {x y: C.obj} (f: C.hom x y): retraction f → epimorphism f :=
  sorry

example {C: Category} {x y: C.obj} (f: C.hom x y): section2 f → monomorphism f :=
  sorry

example {C: Category} {x y: C.obj} (f: C.hom x y): (isomorphism2 f) ↔ (monomorphism f) ∧ (retraction f) :=
  sorry

example {C: Category} {x y: C.obj} (f: C.hom x y): (isomorphism2 f) ↔ (epimorphism f) ∧ (section2 f) :=
  sorry

def opposite (C: Category): Category := {
  obj := C.obj
  hom := fun x y => C.hom y x
  id := C.id
  comp := by intro _ _ _ f g; exact C.comp g f
  id_left := by intros; apply C.id_right
  id_right := by intros; apply C.id_left
  assoc := sorry
}

def Product (C D: Category): Category := {
  obj := C.obj × D.obj
  hom := fun (x1, x2) (y1, y2) => C.hom x1 y1 × D.hom x2 y2
  id := fun (x, y) => (C.id x, D.id y)
  comp := fun (f1, f2) (g1, g2) => (C.comp f1 g1, D.comp f2 g2)
  id_left := by simp; intro _ _ (_, _); simp; apply And.intro; apply C.id_left; apply D.id_left
  id_right := by simp; intro _ _ (_, _); simp; apply And.intro; apply C.id_right; apply D.id_right
  assoc := by simp; intro x y z w f g h; apply And.intro; apply C.assoc; apply D.assoc
}

/- large category? -/
structure CATEGORY where
  obj: Type u
  hom: obj → obj → Type v
  id (a: obj): hom a a
  comp (f: hom a b) (g: hom b c): hom a c
  id_left: ∀ a b: obj, ∀ f: hom a b, f = comp (id a) f
  id_right: ∀ a b: obj, ∀ f: hom a b, f = comp f (id b)
  assoc: ∀ a b c d: obj, ∀ f: hom a b, ∀ g: hom b c, ∀ h: hom c d, comp f (comp g h) = comp (comp f g) h

/- the category of Lean 4 types -/
example: CATEGORY := {
  obj := Type
  hom := fun T1 T2 => T1 → T2
  id := fun _ x => x
  comp := fun f g x => g (f x)
  id_left := by simp
  id_right := by simp
  assoc := by simp /- must be easy to reason about yourself -/
}

def CATEGORY.toCategory (C: CATEGORY): Category := {obj := C.obj, hom := C.hom, id := C.id, comp := C.comp, id_left := C.id_left, id_right := C.id_right, assoc := C.assoc}

/- natural numbers object -/
def NaturalNumberObject (C: Category) (N: C.obj): Prop := by
  have unit: C.obj := sorry
  have z: C.hom unit N := sorry
  have s: C.hom N N := sorry
  exact ∀ N': C.obj, ∀ z': C.hom unit N', ∀ s': C.hom N' N', (∃ x: C.hom N N', (C.comp z x = z') ∧ (C.comp x s' = C.comp s x)) ∧ (sorry) /- missing uniqueness -/
