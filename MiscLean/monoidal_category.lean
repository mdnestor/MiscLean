structure Category where
  obj: Type
  hom: obj -> obj -> Type
  id (a: obj): hom a a
  comp (f: hom a b) (g: hom b c): hom a c
  id_left (f: hom a b): f = comp (id a) f
  id_right (f: hom a b): f = comp f (id b)
  assoc (f: hom a b) (g: hom b c) (h: hom c d): comp f (comp g h) = comp (comp f g) h

structure functor (C D: Category) where
  func0: C.obj -> D.obj
  func1: C.hom x y -> D.hom (func0 x) (func0 y)
  id_preserving (x: C.obj): func1 (C.id x) = D.id (func0 x)
  comp_preserving (f: C.hom x y) (g: C.hom y z): func1 (C.comp f g) = D.comp (func1 f) (func1 g)

structure NaturalTransformation (F G: functor C D) where
  component (x: C.obj): D.hom (F.func0 x) (G.func0 x)
  ok (x y: C.obj) (f: C.hom x y): D.comp (F.func1 f) (component y) = D.comp (component x) (G.func1 f)

def isomorphism {C: Category} {x y: C.obj} (f: C.hom x y): Prop :=
  exists g: C.hom y x, (C.comp f g = C.id x) ∧ (C.comp g f = C.id y)

def natural_isomorphism {C D: Category} {F G: functor C D} (eta: NaturalTransformation F G): Prop :=
  forall x: C.obj, isomorphism (eta.component x)

def Product (C D: Category): Category := {
  obj := C.obj × D.obj
  hom := fun (x1, x2) (y1, y2) => C.hom x1 y1 × D.hom x2 y2
  id := fun (x, y) => (C.id x, D.id y)
  comp := fun (f1, f2) (g1, g2) => (C.comp f1 g1, D.comp f2 g2)
  id_left := by simp; intro _ _ (_, _); simp; apply And.intro; apply C.id_left; apply D.id_left
  id_right := by simp; intro _ _ (_, _); simp; apply And.intro; apply C.id_right; apply D.id_right
  assoc := by simp; intros; apply And.intro; apply C.assoc; apply D.assoc
}

structure MonoidalCategory where
  cat: Category
  bifunctor: functor (Product cat cat) cat
  unit: cat.obj
  /- some natural isomorphisms -/
  associator (a b c: cat.obj): cat.hom (bifunctor.func0 (a, bifunctor.func0 (b, c))) (bifunctor.func0 (bifunctor.func0 (a, b), c))
  left_unitor (a: cat.obj): cat.hom (bifunctor.func0 (unit, x)) x
  right_unitor (a: cat.obj): cat.hom (bifunctor.func0 (x, unit)) x
  /- some natural isomorphism conditions ??? -/

structure Monoid (M: MonoidalCategory) where
  obj: M.cat.obj
  mu: M.cat.hom (M.bifunctor.func0 (obj, obj)) obj
  eta: M.cat.hom M.unit obj
  /- diagrams -/
  pentagon: M.cat.comp (M.bifunctor.func1 (mu, M.cat.id obj)) mu = M.cat.comp (M.associator obj obj obj) (M.cat.comp (M.bifunctor.func1 (M.cat.id obj, mu)) mu)
  unitor_left: M.cat.comp (M.bifunctor.func1 (eta, M.cat.id obj)) mu = M.left_unitor obj
  unitor_right: M.cat.comp (M.bifunctor.func1 (M.cat.id obj, eta)) mu = M.right_unitor obj
  /- confused why these don't work -/
