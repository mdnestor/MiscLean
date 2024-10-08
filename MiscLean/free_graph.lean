-- formalizing free graph
structure Category where
  obj: Type
  hom: obj -> obj -> Type
  id (x: obj): hom x x
  comp {x y z: obj} (f: hom x y) (g: hom y z): hom x z
  assoc: forall x y z w: obj, forall f: hom x y, forall g: hom y z, forall h: hom z w, comp f (comp g h) = comp (comp f g) h
  comp_id_left: forall x y: obj, forall f: hom x y, comp (id x) f = f
  comp_id_right: forall x y: obj, forall f: hom x y, comp f (id y) = f

structure Graph where
  node: Type
  edge: node -> node -> Type

/- tricky -/
structure Path {G: Graph} (x y: G.node) where

axiom Path.empty {G: Graph} (x: G.node): Path x x
axiom Path.edge {G: Graph} (x y: G.node) (e: G.edge x y): Path x y
axiom Path.compose {G: Graph} {x y z: G.node} (p: Path x y) (q: Path y z): Path x z
axiom Path.compose.empty_left {G: Graph}: forall x y: G.node, forall p: Path x y, Path.compose (Path.empty x) p = p
axiom Path.compose.empty_right {G: Graph}: forall x y: G.node, forall p: Path x y, Path.compose p (Path.empty y) = p

noncomputable def FreeGraph (G: Graph): Category := {
  obj := G.node
  hom := fun x y => Path x y
  id := fun x => Path.empty x
  comp := fun p q => Path.compose p q
  assoc := by simp
  comp_id_left := by simp
  comp_id_right := by simp
}
