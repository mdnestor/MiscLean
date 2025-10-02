
structure DynSys where
  state: Type u
  rule: state -> state

structure DynSysMorphism (S1 S2: DynSys) where
  func: S1.state -> S2.state
  conjugate (x: S1.state): func (S1.rule x) = S2.rule (func x)

def DynSysId (S: DynSys): DynSysMorphism S S := {
  func := fun x => x,
  conjugate:= by {intros; simp},
}

def DynSysComp (S1 S2 S3: DynSys) (f1: DynSysMorphism S1 S2) (f2: DynSysMorphism S2 S3) : DynSysMorphism S1 S3 := {
  func := fun x => f2.func (f1.func x),
  conjugate := by {intros; simp; rewrite [f1.conjugate, f2.conjugate]; simp}
}

structure Category where
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

example: Category := {
  obj := DynSys,
  hom := DynSysMorphism
  id := DynSysId
  comp := DynSysComp
  left_id_law := by {intros; rewrite [DynSysComp, DynSysId]; simp},
  right_id_law := by {intros; rewrite [DynSysComp, DynSysId]; simp},
  assoc_law := by {intros; rewrite [DynSysComp, DynSysComp, DynSysComp, DynSysComp]; simp}
}
