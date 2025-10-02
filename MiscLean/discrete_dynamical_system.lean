/-
Discrete-time dynamical systems
-/

structure DynSys where
  state : Type
  rule : state -> state

def simple_system : DynSys := {
  state := Nat,
  rule := λ n => Nat.add n (Nat.succ Nat.zero),
}

structure IVP where
  system : DynSys
  init_state : system.state

def simple_ivp : IVP := {
  system := simple_system,
  init_state := Nat.zero,
}

def solves_ivp (ivp : IVP) (trajectory: Nat -> ivp.system.state) : Prop :=
    (((trajectory 0) = ivp.init_state) ∧ (∀ n : Nat, (trajectory (n + 1)) = ivp.system.rule (trajectory n)))

structure SolvedIVP1 (ivp: IVP) where
  trajectory : Nat -> ivp.system.state
  ok : ((trajectory 0) = ivp.init_state) ∧ (∀ n : Nat, (trajectory (n + 1)) = ivp.system.rule (trajectory n))

structure SolvedIVP2 (system : DynSys) (x0 : system.state) where
  trajectory : Nat -> system.state
  ok : ((trajectory 0) = x0) ∧ (∀ n : Nat, (trajectory (n + 1)) = system.rule (trajectory n))

theorem ivp_solution_is_unique
  (system: DynSys)
  (x0 : system.state)
  (solution1 solution2 : SolvedIVP2 system x0) :
  solution1.trajectory = solution2.trajectory :=
  sorry

structure homomorphism (system1 system2 : DynSys) where
  func : system1.state -> system2.state
  ok : (∀ x : system1.state, (func (system1.rule x) = system2.rule (func x)))

theorem homomorphism_preserves_ivp_solutions
  (system1 system2 : DynSys)
  (f: homomorphism system1 system2)
  (x0 : system1.state)
  (solution1 : SolvedIVP2 system1 x0) :
  SolvedIVP2 system2 (f.func x0) :=
    sorry

def initial_homomorphism (system : DynSys) : (homomorphism simple_system system) :=
  sorry
