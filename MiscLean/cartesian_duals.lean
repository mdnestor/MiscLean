
-- a "discrete time dynamical system"
-- is just a function from a set to itself

structure DynSys (X: Type) where
  map: X → X

-- a pair of coupled dynamical systems
structure DynSysPair (X1 X2 A1 A2: Type) where
  map1: X1 × A1 → X1 × A2
  map2: X2 × A2 → X2 × A1

-- every dual pair on (X1, X2, A1, A2) is a dynsys with state X = X1 × X2 × A1 × A2
def pair_to_sys (S: DynSysPair X1 X2 A1 A2): DynSys (X1 × X2 × A1 × A2) := {
  map := fun ⟨x1, x2, a1, a2⟩ => by {
    let y1 := S.map1 ⟨x1, a1⟩
    let y2 := S.map2 ⟨x2, a2⟩
    exact ⟨y1.1, y2.1, y2.2, y1.2⟩
  }
}

-- if the state space can be represented as a product,
-- there is trivial representation as coupled pair, take A1 = X2 and A2 = X1
example (S: DynSys (X1 × X2)): DynSysPair X1 X2 X2 X1 := {
  map1 := fun ⟨x1, x2⟩ => by {
    let y := S.map ⟨x1, x2⟩
    exact ⟨y.1, y.1⟩
  }
  map2 := fun ⟨x2, x1⟩ => by {
    let y := S.map ⟨x1, x2⟩
    exact ⟨y.2, y.2⟩
  }
}

-- another minimal example: parallel system
def parallel (S1: DynSys X1) (S2: DynSys X2): DynSys (X1 × X2) := {
  map := fun ⟨x1, x2⟩ => ⟨S1.map x1, S2.map x2⟩
}

-- two systems in parallel interact as a pair trivially via the singleton type
def parallel_decomp (S1: DynSys X1) (S2: DynSys X2): DynSysPair X1 X2 Unit Unit := {
  map1 := fun ⟨x1, _⟩ => ⟨S1.map x1, Unit.unit⟩
  map2 := fun ⟨x2, _⟩ => ⟨S2.map x2, Unit.unit⟩
}

-- idea: define some notion of channel capacity
-- then a cartesian dual decomposition is "useful" if strictly |A1| < |X2| or |A2| < |X1|

-- trivial example: 2 body problem
-- let P = R^d and V = R^d be the spaces of possible positions and velocities
-- the global state space is X = (P x V)^2
-- the local state spaces are X1 = X2 = P x V
-- and the channels are A1 = A2 = P carrying only information about position
