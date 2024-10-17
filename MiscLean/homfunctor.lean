-- hom functor

structure Category where
  Obj: Type u
  Hom: Obj → Obj → Type v
  id (x: Obj): Hom x x
  comp (f: Hom x y) (g: Hom y z): Hom x z
  assoc: comp (comp f g) h = comp f (comp g h)
  id_comp {f: Hom x y}: comp (id x) f = f
  comp_id {f: Hom x y}: comp f (id y) = f

def Set: Category := {
  Obj := Type
  Hom := fun X Y => X → Y
  id := @id
  comp := flip Function.comp
  assoc := by
    intros
    ext
    rfl
  id_comp := by
    intros
    ext
    rfl
  comp_id := by
    intros
    ext
    rfl
}

structure functor (C D: Category) where
  obj: C.Obj → D.Obj
  hom: C.Hom x y → D.Hom (obj x) (obj y)
  ok: hom (C.comp f g) = D.comp (hom f) (hom g)

--  covariant hom functor
def HomFunctor (A: C.Obj): functor C Set := {
  obj := C.Hom A
  hom := flip C.comp
  ok := by
    intros
    simp [Set]
    ext
    simp [flip]
    rw [←C.assoc]
}

def opposite (C: Category): Category := {
  Obj := C.Obj
  Hom := fun X Y => C.Hom Y X
  id := C.id
  comp := flip C.comp
  assoc := by simp [flip, C.assoc]
  id_comp := C.comp_id
  comp_id := C.id_comp
}

-- contravariant hom functor
def CoHomFunctor (B: C.Obj): functor (opposite C) Set := {
  obj := (flip C.Hom) B
  hom := C.comp
  ok := by
    intros
    simp [Set]
    ext
    rw [flip]
    simp [opposite]
    rw [←C.assoc, flip]
}
