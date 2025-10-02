
structure Monoid where
  elem: Type
  id: elem
  op: elem -> elem -> elem
  left_id_law (x: elem): op e x = x
  right_id_law (x: elem): op e x = x
  assoc_law (x y z: elem): op x (op y z) = op (op x y) z

structure MonoidHomomorphism (M1 M2: Monoid) where
  func: M1.elem -> M2.elem
  id_preserving: func M1.id = M2.id
  op_preserving (x y: M1.elem): func (M1.op x y) = M2.op (func x) (func y)

def id_morphism (M: Monoid) : MonoidHomomorphism M M := {
  func := fun x => x,
  id_preserving := rfl,
  op_preserving := by {intros; simp}
}

def comp_morphism (M1 M2 M3: Monoid) (f1: MonoidHomomorphism M1 M2) (f2: MonoidHomomorphism M2 M3): MonoidHomomorphism M1 M3 := {
  func := fun x => f2.func (f1.func x),
  id_preserving := by {intros; simp; rewrite [f1.id_preserving, f2.id_preserving]; rfl},
  op_preserving := by {intros; simp; rewrite [f1.op_preserving, f2.op_preserving]; rfl}
}

structure Category where
  obj: Type u
  hom (_ _: obj): Type v
  id (a: obj): hom a a
  comp (a b c: obj) (f: hom a b) (g: hom b c): hom a c
  left_id_law (a b: obj) (f: hom a b):
    f = comp a a b (id a) f
  right_id_law (a b: obj) (f: hom a b):
    f = comp a b b f (id b)
  assoc_law (a b c d: obj) (f: hom a b) (g: hom b c) (h: hom c d):
    comp a b d f (comp b c d g h) = comp a c d (comp a b c f g) h

example: Category := {
  obj := Monoid,
  hom := by {intro M1 M2; exact MonoidHomomorphism M1 M2},
  id := by {intro M; exact id_morphism M},
  comp := by {intro M1 M2 M3 f1 f2; exact comp_morphism M1 M2 M3 f1 f2},
  left_id_law := by {intros; rewrite [comp_morphism, id_morphism]; simp},
  right_id_law := by {intros; rewrite [comp_morphism, id_morphism]; simp},
  assoc_law := by {intros; rewrite [comp_morphism, comp_morphism, comp_morphism, comp_morphism]; simp}
}
