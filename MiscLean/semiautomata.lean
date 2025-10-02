/-
this file:
- defines semiautomata as state machines with an input alphabet
- defines the action of the free monoid of the input alphabet
- defines the reachability relation and shows it forms a preorder
-/

-- A semiautomaton consists of a state set, input set, and transition map
structure Semiautomaton where
  state: Type
  input: Type
  update: input → state → state

-- run takes a list of inputs and returns the corresponding state → state map
def run {M: Semiautomaton} (inputs: List M.input): M.state → M.state :=
  match inputs with
  | [] => fun s => s
  | head :: tail => fun s => run tail (M.update head s)

-- appending lists of inputs corresponds to composing run maps
theorem semiautomaton_append_compose (M: Semiautomaton) (inputs0 inputs1: List M.input): run (List.append inputs0 inputs1) = Function.comp (run inputs1) (run inputs0) := by
  induction inputs0 with
  | nil =>
    ext s
    rw [run, List.append, Function.comp]
  | cons head tail ih =>
    simp [run, List.append, Function.comp]
    ext s
    rw [← List.append_eq]
    rw [congrFun ih (M.update head s)]
    simp

-- the input monoid

structure Monoid where
  elt: Type
  op: elt → elt → elt
  unit: elt
  assoc: ∀ x y z: elt, op (op x y) z = op x (op y z)
  unit_left: ∀ x: elt, op unit x = x
  unit_right: ∀ x: elt, op x unit = x

structure RightMonoidAction (M: Monoid) (X: Type) where
  act: M.elt → X → X
  preserve: ∀ m0 m1: M.elt, ∀ x: X, act m1 (act m0 x) = act (M.op m0 m1) x

def FreeMonoid (A: Type): Monoid := {
  elt := List A
  op := List.append
  unit := []
  assoc := List.append_assoc
  unit_left := List.nil_append
  unit_right := List.append_nil
}

-- every semiautomaton corresponds to a (right) action of the free monoid on its inputs acting on its state
def InputMonoid (M: Semiautomaton): RightMonoidAction (FreeMonoid M.input) M.state := {
  act := fun inputs s => run inputs s
  preserve := by
    intro inputs1 inputs2 s
    simp [FreeMonoid]
    rw [←List.append_eq_append]
    rw [semiautomaton_append_compose]
    rw [Function.comp]
}

-- the reachability relation: given states s0 and s1, s0 can reach s1 if there exists a sequence of inputs mapping s0 to s1
def reach {M: Semiautomaton} (s0 s1: M.state): Prop :=
  ∃ inputs: List M.input, run inputs s0 = s1

-- any state can reach itself via the empty list of inputs
theorem reach_reflexive {M: Semiautomaton} (s: M.state): reach s s := by
  exists []

-- if s0 can reach s1 and s1 can reach s2 then s0 can reach s2 via concatenating inputs
theorem reach_transitive {M: Semiautomaton} (s0 s1 s2: M.state): reach s0 s1 ∧ reach s1 s2 → reach s0 s2 := by
  intro ⟨h0, h1⟩
  obtain ⟨as0, h2⟩ := h0
  obtain ⟨as1, h3⟩ := h1
  exists List.append as0 as1
  rw [semiautomaton_append_compose]
  rw [Function.comp]
  rw [h2, h3]
  
-- https://en.wikipedia.org/wiki/Preorder
structure Preorder (X: Type) where
  leq: X → X → Prop
  reflexive: ∀ x: X, leq x x
  transitive: ∀ x y z: X, (leq x y) ∧ (leq y z) → leq x z

-- the reach relation defines a preorder on the states of a semiautomaton
example (M: Semiautomaton): Preorder M.state := {
  leq := reach
  reflexive := reach_reflexive
  transitive := reach_transitive
}
