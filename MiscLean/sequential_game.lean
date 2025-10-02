-- A "preference" relation on a type X. Here it is just a preorder
structure Pref (X: Type) where
  rel: X → X → Prop
  refl: ∀ x, rel x x
  trans: ∀ x y z, rel x y → rel y z → rel x z

-- the "pullback" of a preorder on Y along a function f: X → Y and returns a preorder on X
def pullback {X Y: Type} (f: X → Y) (p: Pref Y): Pref X := {
  rel := fun x1 x2 => p.rel (f x1) (f x2)
  refl := by intro x; exact p.refl (f x)
  trans := by intro x y z; exact p.trans (f x) (f y) (f z)
}

-- definition of a normal form game: a set of players, a set of strategies and each player has a preference over strategy profiles
structure Game where
  player: Type
  strategy: Type
  pref: player → Pref (player → strategy)

-- a sequential game: a set of players, actions, and types
-- "turn" tells whose turn it is from a given state
-- "move" takes state and an action and returns the next state
-- "pref" every player has a preference relation on game state sequences
structure SequentialGame where
  player: Type
  state: Type
  action: Type
  turn: state → player
  move: action → state → state
  pref: player → Pref (Nat → state)

-- given a sequential game, an initial state s0, and a strategy for each player. Returns the sequence s0, s1, s2, ... of resulting gameplay.
def play (G: SequentialGame) (s0: G.state) (π: G.player → G.state → G.action): Nat → G.state :=
  fun n => match n with
  | Nat.zero => s0
  | Nat.succ m =>
    let s := play G s0 π m
    G.move (π (G.turn s) s) s

-- we can turn a sequential game into a normal form game by pulling back along the "play" function :)
example (G: SequentialGame) (s0: G.state): Game := {
  player := G.player
  strategy := G.state → G.action
  pref := fun i => pullback (play G s0) (G.pref i)
}

-- bonus

-- "update" a function at a point
def update {X Y: Type} [DecidableEq X] (f: X → Y) (x0: X) (y0: Y): X → Y :=
  fun x => if x = x0 then y0 else f x

-- a strategy profile is a nash equilirbium if every player would not prefer to do something different 
def NashEquilibrium (G: Game) [DecidableEq G.player] (π: G.player → G.strategy): Prop :=
  ∀ i s, (G.pref i).rel (update π i s) π
