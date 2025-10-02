def Subset (T: Type) : Type := T -> Prop
def subseteq (T: Type) (U V: Subset T): Prop := forall x, (U x) -> (V x)
def image (T1 T2: Type) (f: T1 -> T2) (U: Subset T1): Subset T2 := fun y => exists x, (U x) ∧ (f x = y)

/- Abstract simplicial complex -/
structure SimplicialComplex where
  point: Type
  face: Subset (Subset point)
  ok (A B: Subset point) (h1: face B) (h2: subseteq point A B): face A

structure SimplicialMap (C1 C2: SimplicialComplex) where
  func: C1.point -> C2.point
  ok (F: Subset C1.point) (h: C1.face F): C2.face (image C1.point C2.point func F)
