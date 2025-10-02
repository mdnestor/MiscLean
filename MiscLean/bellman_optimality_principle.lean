import Mathlib.Topology.Instances.ENNReal

structure DecisionProblem where
  state: Type
  action: Type
  transition: state → action → state
  utility: state → action → Real

-- run maps a state and an action sequence to the resulting state sequence
def run (P: DecisionProblem) (s0: P.state) (as: Nat → P.action): Nat → P.state :=
  fun n => match n with
  | Nat.zero => s0
  | Nat.succ p => P.transition (run P s0 as p) (as p)

-- Given an initial state s0, the value of an action sequence is the summed utility of all future (state, action) pairs (possibly infinite)
noncomputable def ActionSequenceValue {P: DecisionProblem} (s0: P.state) (as: Nat → P.action): Real :=
  ∑' (n : ℕ), P.utility (run P s0 as n) (as n)

-- The value of a state is the maximum action sequence value with respect to all possible action sequences
noncomputable def StateValue {P: DecisionProblem} (s0: P.state): Real :=
  sSup (Set.image (fun as => ActionSequenceValue s0 as) Set.univ)

-- The Bellman optimality principle says the value of a state is equal to the maximum over all possible actions plus the value of the next state resulting from that action
theorem BellmanOptimalityPrinciple {P: DecisionProblem} (s0: P.state): StateValue s0 = sSup (Set.image (fun a: P.action => (P.utility s0 a) + StateValue (P.transition s0 a)) Set.univ) := by
  sorry
