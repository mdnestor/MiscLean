class Category where
  obj: Type u
  hom: obj → obj → Type v
  comp (f: hom x y) (g: hom y z): hom x z
  id (x: obj): hom x x
  id_comp (x y: obj) (f: hom x y): comp (id x) f = f 
  comp_id (x y: obj) (f: hom x y): comp f (id y) = f 
  comp_assoc (x y z: obj) (f: hom x y) (g: hom y z) (h: hom z w): comp (comp f g) h = comp f (comp g h)

class functor (C D: Category) where
  obj: C.obj → D.obj
  hom: C.hom x y → D.hom (obj x) (obj y)
  id (x: C.obj): hom (C.id x) = D.id (obj x)
  comp (x y z: C.obj) (f: C.hom x y) (g: C.hom y z): hom (C.comp f g) = D.comp (hom f) (hom g)

def functor_comp {C D E: Category} (F: functor C D) (G: functor D E): functor C E := {
  obj := G.obj ∘ F.obj
  hom := fun f => G.hom (F.hom f)
  id := by intro; simp [F.id, G.id]
  comp := by intros; simp [F.comp, G.comp]
}

def functor_id (C: Category): functor C C := {
  obj := id
  hom := id
  id := by simp
  comp := by simp
}

def Categories: Category where
  obj := Category
  hom := functor
  comp := functor_comp
  id := functor_id
  id_comp := by intros; rfl
  comp_id := by intros; rfl
  comp_assoc := by intros; rfl
