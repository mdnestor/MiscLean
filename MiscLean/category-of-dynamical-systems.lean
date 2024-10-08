

structure Monoid where
  elem: Type
  id: elem
  op: elem -> elem -> elem
  left_id_law (x: elem): op e x = x
  right_id_law (x: elem): op e x = x
  assoc_law (x y z: elem): op x (op y z) = op (op x y) z

structure MonoidMorphism (M1 M2: Monoid) where
  func: M1.elem -> M2.elem
  id_law: func M1.id = M2.id
  op_law (x y: M1.elem): func (M1.op x y) = M2.op (func x) (func y)

def Monoid_id (M: Monoid) : MonoidMorphism M M := {
  func := fun x => x,
  id_law := rfl,
  op_law := by {intros; simp}
}

def Monoid_comp (M1 M2 M3: Monoid) (f1: MonoidMorphism M1 M2) (f2: MonoidMorphism M2 M3): MonoidMorphism M1 M3 := {
  func := fun x => f2.func (f1.func x),
  id_law := by {intros; simp; rw [f1.id_law, f2.id_law]},
  op_law := by {intros; simp; rw[f1.op_law, f2.op_law]}
}

/- Define a dynamical system as the action of a monoid -/
structure DynSys where
  state: Type
  time: Monoid
  rule: time.elem -> state -> state
  id_law (x: state): rule time.id x = x
  action_law (x: state) (t1 t2: time.elem): rule t2 (rule t1 x) = rule (time.op t2 t1) x

/- Homomorphism of dynamical systems -/
structure DynSysMorphism (S1 S2: DynSys) where
  func: S1.state -> S2.state
  morphism: MonoidMorphism S1.time S2.time
  ok (x: S1.state) (t: S1.time.elem): func (S1.rule t x) = S2.rule (morphism.func t) (func x)

def dynsys_id (S: DynSys) : DynSysMorphism S S := {
  func := fun x => x,
  morphism := Monoid_id S.time
  ok := by {intros; rfl}
}
def dynsys_comp (S1 S2 S3: DynSys) (f1: DynSysMorphism S1 S2) (f2: DynSysMorphism S2 S3): DynSysMorphism S1 S3 := {
  func := fun x => f2.func (f1.func x),
  morphism := Monoid_comp S1.time S2.time S3.time f1.morphism f2.morphism,
  ok := by {intros; simp; rw [Monoid_comp, f1.ok, f2.ok]}
}

structure Cat where
  obj: Type u
  hom (_ _: obj) : Type v
  id (a: obj): hom a a
  comp (a b c: obj) (f: hom a b) (g: hom b c): hom a c
  left_id_law (a b: obj) (f: hom a b):
    f = comp a a b (id a) f
  right_id_law (a b: obj) (f: hom a b):
    f = comp a b b f (id b)
  assoc_law (a b c d: obj) (f: hom a b) (g: hom b c) (h: hom c d):
    comp a b d f (comp b c d g h) = comp a c d (comp a b c f g) h

def category_of_Monoidoids: Cat := {
  obj := Monoid,
  hom := by {intro M1 M2; exact MonoidMorphism M1 M2},
  id := by {intro M; exact Monoid_id M},
  comp := by {intro M1 M2 M3 f1 f2; exact Monoid_comp M1 M2 M3 f1 f2},
  left_id_law := by {intros; rw [Monoid_comp, Monoid_id]},
  right_id_law := by {intros; rw [Monoid_comp, Monoid_id]},
  assoc_law := by {intros; rw [Monoid_comp, Monoid_comp, Monoid_comp, Monoid_comp]}
}

def category_of_dynamical_systems: Cat := {
  obj := DynSys,
  hom := by {intro S1 S2; exact DynSysMorphism S1 S2},
  id := by {intro S; exact dynsys_id S},
  comp := by {intro S1 S2 S3 f1 f2; exact dynsys_comp S1 S2 S3 f1 f2},
  left_id_law := by {intros; rfl},
  right_id_law := by {intros; rfl},
  assoc_law := by {intros; rfl}
}
