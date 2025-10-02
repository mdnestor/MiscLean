
structure Preorder where
  element: Type
  leq: element -> element -> Prop
  p1: forall x: element, leq x x
  p2: forall x y z: element, leq x y ∧ leq y z -> leq x z

def Preorder.lt {P: Preorder} (x y: P.element): Prop :=
  (P.leq x y) ∧ (x ≠ y)

structure ParetoGame where
  state: Type
  player: Type
  outcome: Preorder
  play: state -> player -> outcome.element

def ParetoImprovement {G: ParetoGame} (x y: G.state): Prop :=
  forall p: G.player, G.outcome.leq (G.play x p) (G.play y p)

def ParetoEfficient {G: ParetoGame} (x: G.state): Prop := 
  forall y: G.state, ¬ ParetoImprovement x y

def ParetoDominated {G: ParetoGame} (x: G.state): Prop := ¬ ParetoEfficient x

def StrongParetoImprovement {G: ParetoGame} (x y: G.state): Prop :=
  forall p: G.player, G.outcome.lt (G.play x p) (G.play y p)

def WeakParetoEfficient {G: ParetoGame} (x: G.state): Prop :=
  forall y: G.state, ¬ StrongParetoImprovement x y

theorem StrongParetoImprovementIsParetoImprovement: forall G: ParetoGame, forall x y: G.state, StrongParetoImprovement x y -> ParetoImprovement x y := by
  intro G x y;
  rw [StrongParetoImprovement, ParetoImprovement]
  intro h p
  sorry

theorem ParetoEfficientIsWeakParetoEfficient: forall G: ParetoGame, forall x: G.state, ParetoEfficient x -> WeakParetoEfficient x := by
  intro G x
  rw [ParetoEfficient, WeakParetoEfficient]
  intro h y
  sorry

def subset (X: Type): Type := X -> Prop

def ParetoFront (G: ParetoGame): subset G.state :=
  fun x => ParetoEfficient x

def WeakParetoFront (G: ParetoGame): subset G.state :=
  fun x => WeakParetoEfficient x
