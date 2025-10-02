structure DetMach where /- Deterministic machine -/
  state: Type
  input: Type
  rule: input -> state -> state
def DetMach.stream (M: DetMach) (initial: M.state) (inputs: List M.input): M.state :=
  match inputs with
  | List.nil => initial
  | List.cons input_head input_tail => M.rule input_head (DetMach.stream M initial input_tail)
def DetMach.reachable (M: DetMach) (initial target: M.state): Prop :=
  ∃ inputs: List M.input, (DetMach.stream M initial inputs) = target
def Subset (T: Type) : Type := T -> Prop
def Subset.union (T: Type) (U V: Subset T): Subset T := fun x => (U x) ∨ (V x)
def Subset.inter (T: Type) (U V: Subset T): Subset T := fun x => (U x) ∧ (V x)
def Subset.neg (T: Type) (U: Subset T): Subset T := fun x => ¬ U x
structure Mach where /- Nondeterministic machine -/
  state: Type
  input: Type
  rule: input -> state -> Subset state
def Mach.apply_stream (M: Mach) (initial: Subset M.state) (inputs: List M.input): Subset M.state :=
  match inputs with
  | List.nil => initial
  | List.cons input_head input_tail => Mach.apply_stream M (fun x => ∃ s: M.state, M.rule input_head s x) input_tail
/- For a non-deterministic machine, given two subsets of state space A and B, A can reach B if there exists a sequence of inputs and a point in A and the result lies in B -/
def Mach.reachable (M: Mach) (A B: Subset M.state): Prop :=
  ∃ input_seq: List M.input, ∃ x: M.state, (Mach.apply_stream M A input_seq x) ∧ (B x)

/- Given a starting set I and a "safe" set P, determine if the machine M is safe -/
/- in other words, the complement of the safe set is not reachable -/
def Mach.safe (M: Mach) (I P: Subset M.state): Prop := ¬ Mach.reachable M I (Subset.neg M.state P)
/- First attempt to build machine graph -/
/- Nodes and edges are two arbitrary types along with first and second maps -/
universe u v
structure DirectedGraph where
  node: Type u
  edge: Type v
  fst: edge -> node
  snd: edge -> node
structure MachEdge where /- Dom uses the machine to edge the codom -/
  dom: Type
  codom: Type
  input: Type
  func: input -> dom -> Subset codom
def MachGraph  : DirectedGraph := {
  node := Type,
  edge := MachEdge,
  fst := fun x => x.dom,
  snd := fun x => x.codom
}
structure GraphMorphism (G1 G2: DirectedGraph) where
  node_map: G1.node -> G2.node
  edge_map: G1.edge -> G2.edge
  compatibility_fst: node_map ∘ G1.fst = G2.fst ∘ edge_map
  compatibility_snd: node_map ∘ G1.snd = G2.snd ∘ edge_map
def LocalState (G: DirectedGraph) (world: GraphMorphism G MachGraph) (x: G.node): Type := world.node_map x
def We (G: DirectedGraph) (world: GraphMorphism G MachGraph) (x y: G.node) (e: G.edge) (_: G.fst e = x ∧ G.snd e = y): MachEdge := world.edge_map e
def TotalMachine (G: DirectedGraph) (W: GraphMorphism G MachGraph): Mach := {
  state := sorry, /- ??? -/
  input := sorry,
  rule := sorry,
}
def embed_substate_space (G: DirectedGraph) (W: GraphMorphism G MachGraph) (x: G.node) (S: Subset (W.node_map x)): Subset (TotalMachine G W).state := sorry
def LocallySafeInAGlobalContext (G: DirectedGraph) (W: GraphMorphism G MachGraph) (x: G.node) (I P: Subset (LocalState G W x)): Prop := Mach.safe (TotalMachine G W) (embed_substate_space G W x I) (embed_substate_space G W x P)

/- Alternative: edges are dependent types. idk -/
structure DirectedGraph2 where
  node: Type u
  edge (_ _: node): Type v
structure MachEdge2 (T1 T2: Type) where /- Dom uses the machine to edge the codom -/
  input: Type
  func: input -> T1 -> Subset T2
def MachGraph2: DirectedGraph2 := {
  node := Type,
  edge := by {intro T1 T2; exact MachEdge2 T1 T2}
}
structure GraphMorphism2 (G1 G2: DirectedGraph2) where
  node_map: G1.node -> G2.node
  edge_hom (n1 n2: G1.node): G1.edge n1 n2 -> G2.edge (node_map n1) (node_map n2)
def LocalState2 (G: DirectedGraph2) (world: GraphMorphism2 G MachGraph2) (x: G.node): Type := world.node_map x
def We2 (G: DirectedGraph2) (world: GraphMorphism2 G MachGraph2) (x y: G.node) (e: G.edge x y): MachEdge2 (world.node_map x) (world.node_map y) := world.edge_hom x y e
def TotalMachine2 (G: DirectedGraph2) (W: GraphMorphism2 G MachGraph2): Mach := {
  state := sorry,
  input := sorry,
  rule := sorry,
}/- to define global context we need embedding of the local subset of state space into the global state space -/
def embed_substate_space2 (G: DirectedGraph2) (W: GraphMorphism2 G MachGraph2) (x: G.node) (S: Subset (W.node_map x)): Subset (TotalMachine2 G W).state := sorry
def LocallySafeInAGlobalContext2 (G: DirectedGraph2) (W: GraphMorphism2 G MachGraph2) (x: G.node) (I P: Subset (LocalState2 G W x)): Prop := Mach.safe (TotalMachine2 G W) (embed_substate_space2 G W x I) (embed_substate_space2 G W x P)


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

/- going to fix a global hgraph now-/

def G : DirectedGraph2:= sorry
structure Path (x y: G.node) where
  edges : List (G.edge x y)
  valid : sorry /- should ensure edges[i].snd = edges[i+1].fst -/

def FreeCat : Cat := {
  obj:= G.node,
  hom := by {intro x y; exact Path x y},
  id := sorry,
  comp := sorry,
  left_id_law := sorry,
  right_id_law  := sorry,
  assoc_law  := sorry,
}
