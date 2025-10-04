
set_option linter.unusedSectionVars false

def Relation (X Y: Type): Type :=
  X → Y → Prop

def Prefer (X: Type): Type :=
  Relation X X

def reflexive {X: Type} (prefer: Prefer X): Prop :=
  ∀ x, prefer x x

def antisymmetric {X: Type} (prefer:  Prefer X): Prop :=
  ∀ x y, prefer x y → prefer y x → x = y

/-

First definition of a normal-form game based on the notion of utility, consisting of:

- a set of players,
- a set of strategies (assumed to be the same for all players),
- a set of possible 'utility' values,
- a 'play' function which maps strategy profiles to utility profiles, where
  - a 'strategy profile' is a choice of strategy for each player,
  - a 'utility profile' is an assignment of utilities to each player; and
- a preference relation on utility values, assumed to be shared by all players.

For example the utility could be a numerical value
and all players agree "more is better" (for themselves).

Note the 'play' function wraps what is usually called the 'payoff matrix'.

-/

class UtilityGame (P S U: Type) where
  play: (P → S) → (P → U)
  prefer: Prefer U

-- A generalization: instead of each player getting a utility,
-- the game has some 'outcome' and the players have a preference on outcomes.

class OutcomeGame (P S O: Type) where
  play: (P → S) → O
  prefer:  P → Prefer O

variable {P S O U: Type} [DecidableEq P]

-- Every utility game is an outcome game where the outcomes are utility assignments
-- and players prefer outcomes where they get higher utility.

def UtilityGame.toOutcomeGame (G: UtilityGame P S U): OutcomeGame P S (P → U) := {
  play := G.play
  prefer := fun p => fun π0 π1 => G.prefer (π0 p) (π1 p)
}

-- One more further disillation: we don't need to explicitly reference the set of outcomes.
-- Instead, the players can have preferences directly on strategy profiles.

class Game (P S: Type) where
  prefer: P → Prefer (P → S)

-- This is actually an equivalent representation because we can treat the strategy profiles themselves as outcomes.
def OutcomeGame.toGame (G: OutcomeGame P S O): Game P S := {
  prefer := fun p => fun π0 π1 => G.prefer p (G.play π0) (G.play π1)
}

def UtilityGame.toGame (G: UtilityGame P S U): Game P S :=
  G.toOutcomeGame.toGame

def Game.toOutcomeGame (G: Game P S): OutcomeGame P S (P → S) := {
  play   := id
  prefer := G.prefer
}



-- To define concepts like dominant strategies and best response, we will frequently use the following helper:
-- given a function f: X → Y and a pair (x0, y0) we can "update" f to take the value f(x0) = y0.

def update (π: P → S) (p0: P) (s0: S): P → S :=
  fun p => if p = p0 then s0 else π p

-- Given a fixed strategy profile, a strategy is called a player's 'best response'
-- if no other strategy is better in that profile.

def best_response (G: Game P S) (π: P → S) (p: P) (s: S): Prop :=
  ∀ s', G.prefer p (update π p s') (update π p s)

-- A Nash equilibrium is a profile in which every player is using their best response.

def nash_equilibrium (G: Game P S) (π: P → S): Prop :=
  ∀ p, best_response G π p (π p)

-- For a fixed player, a strategy s 'dominates' another strategy s0 if it's always preferable to play s over s0.
-- The strategy s is called 'dominant' if it dominates all other strategies.

def dominates (G: Game P S) (p: P) (s0 s: S): Prop :=
  ∀ π, G.prefer p (update π p s0) (update π p s)

def dominant (G: Game P S) (p: P) (s: S): Prop :=
  ∀ s0, dominates G p s0 s

-- Some immediately obvious theorems:
-- A strategy is dominant iff. it is the best response to every profile (this is basically just by definition).

theorem dominant_iff_best_response (G: Game P S) (p: P) (s: S): dominant G p s ↔ ∀ π, best_response G π p s := by
  exact forall_comm

-- Any profile where every player is using a dominant strategy is a Nash equilibrium.

theorem dominant_equilibrium (G: Game P S) (π: P → S) (h: ∀ p, dominant G p (π p)): nash_equilibrium G π := by
  intro p s
  exact h p s π

/-

Example: prisoner's dilemma.

It is a utility game with
- two players
- two strategies, defect or not
- four possible scores / utilities - sometimes described as costs / negative utilities, e.g. prison sentences

We can model the players as {0, 1} and the strategies as {false, true} with true = defect,
and the payoffs as 0, 1, 2, 3. Maybe 0 = death, 1 = prison, 2 = probation, and 3 = freedom.
Here is the payoff matrix (i.e. the play function) with (u0, u1) the utilities of players 0 and 1 respectively:

                           Player 1
                     cooperate   defect
                    --------------------
          cooperate | (2, 2)  |  (0, 3)
Player 0            |-------------------
          defect    | (3, 0)  |  (1, 1)

-/

def PrisonerDilemma: UtilityGame (Fin 2) Bool (Fin 4) := {
  play := fun π => fun p => match (π 0, π 1) with
    -- neither defect
    | (false, false) => match p with
      | 0 => 2
      | 1 => 2
    -- first defects
    | (true, false) => match p with
      | 0 => 3
      | 1 => 0
    -- second defects
    | (false, true) => match p with
      | 0 => 0
      | 1 => 3
    -- both defect
    | (true, true) => match p with
      | 0 => 1
      | 1 => 1
  prefer := fun u1 u2 => u1 ≤ u2
}

-- In the prisoner's dilemma, the Nash equilibrium is for both to defect.

example: nash_equilibrium PrisonerDilemma.toGame (fun _ => true) := by
  intro p s
  rw [PrisonerDilemma, UtilityGame.toGame, UtilityGame.toOutcomeGame, OutcomeGame.toGame]
  simp [update]
  change Fin 2 at p
  change Bool at s
  match p with
  | 0 => cases s <;> simp
  | 1 => cases s <;> simp

-- Given a preference, there is the associated "strict" preference
-- and all the associated notions

def strict {U: Type} (prefer: Prefer U): Prefer U :=
  fun u1 u2 => prefer u1 u2 ∧ ¬ prefer u2 u1

def strict_best_response (G: Game P S) (π: P → S) (p: P) (s: S): Prop :=
  ∀ s', s ≠ s' → strict (G.prefer p) (update π p s') (update π p s)

def strict_nash_equilibrium (G: Game P S) (π: P → S): Prop :=
  ∀ p, best_response G π p (π p)

def strict_dominates (G: Game P S) (p: P) (s0 s: S): Prop :=
  ∀ π, strict (G.prefer p) (update π p s0) (update π p s)

def strict_dominant (G: Game P S) (p: P) (s: S): Prop :=
  ∀ s0, strict_dominates G p s0 s

-- When strict best response / Nash equilibria / dominant strategies exist, they are unique.

theorem strict_best_response_unique {G: Game P S} {π: P → S} {p: P} {s s': S} (h1: strict_best_response G π p s) (h2: strict_best_response G π p s'): s = s' := by
  sorry

theorem strict_nash_equilibrium_unique {G: Game P S} {π π': P → S} (h1: strict_nash_equilibrium G π) (h2: strict_nash_equilibrium G π'): π = π' := by
  sorry

theorem strict_dominant_unique {G: Game P S} {p: P} {s s': S} (h1: strict_dominant G p s) (h2: strict_dominant G p s'): s = s' := by
  sorry



-- Given an indexed collection P_1, P_2, ..., P_n of individual preferences on X,
-- the Pareto preference is defined by x ≤ y iff. every individual prefers x ≤ y.

def pareto {X I: Type} (prefer:  I → Prefer X): Prefer X :=
  fun x1 x2 => ∀ i, prefer i x1 x2

-- A profile π1 Pareto dominates π0 if every player prefers π1.
-- It is Pareto dominant if it Pareto dominates every other strategy.
-- Likewise for strict Pareto dominates.

def pareto_dominates (G: Game P S) (π0 π1: P → S): Prop :=
  pareto G.prefer π0 π1

def pareto_dominant (G: Game P S) (π: P → S): Prop :=
  ∀ π0, pareto_dominates G π0 π

def strict_pareto_dominates (G: Game P S) (π0 π1: P → S): Prop :=
  strict (pareto G.prefer) π0 π1

def strict_pareto_dominant (G: Game P S) (π: P → S): Prop :=
  ∀ π0, strict_pareto_dominates G π0 π

-- π1 strictly Pareto dominates π0 iff. everyone weakly prefer π1, and someone strongly prefers π1.

theorem strict_pareto_dominates_iff (G: Game P S) (π0 π1: P → S): strict_pareto_dominates G π0 π1 ↔ (∀ p, G.prefer p π0 π1) ∧ (∃ p, ¬ G.prefer p π1 π0) := by
  simp [strict_pareto_dominates]
  constructor
  · intro h
    constructor
    · exact h.1
    · have := h.2
      simp [pareto] at this
      exact this
  · intro h
    constructor
    · intro i
      exact h.1 i
    · simp [pareto]
      exact h.2

-- A profile is Pareto efficient if it is not strictly Pareto dominated.

def pareto_efficient (G: Game P S) (π: P → S): Prop :=
  ∀ π1, ¬ strict_pareto_dominates G π π1

-- A zero-sum game is one where preferences are flipped between different players.

def zero_sum (G: Game P S): Prop :=
  ∀ p1 p2 π1 π2, p1 ≠ p2 → (G.prefer p1 π1 π2 ↔ G.prefer p2 π2 π1)

/-

In a zero-sum game with at least 2 players and all preferences reflexive and anti-symmetric,
every strategy profile is Pareto efficient.

Proof:
- Suppose for contradiction π is not Pareto efficient.
- Then there exists strict Pareto improvement π'.
- So any two distinct players p1, p2 weakly prefer π ≤ π'.
- By zero sum, since p1 weakly prefers π ≤ π' then p2 weakly prefers π' ≤ π.
- By reflexivity π = π'.
- But since π' is a strict improvement, some player p3 strictly prefers π < π' = π, contradiction.

-/

theorem zero_sum_pareto_efficient (G: Game P S) (h1: zero_sum G) (h2: ∀ p, reflexive (G.prefer p)) (h3: ∀ p, antisymmetric (G.prefer p)) (h4: ∀ p: P, ∃ p': P, p ≠ p'): ∀ π: P → S, pareto_efficient G π := by
  intro π π' h_strict
  simp_all [strict_pareto_dominates, strict, pareto]
  obtain ⟨p1, h_p1_not_prefer_π⟩ := h_strict.2
  obtain ⟨p2, h_p1_neq_p2⟩ := h4 p1
  have h_p1_prefer_π' := h_strict.1 p1
  have h_p2_prefer_π' := h_strict.1 p2
  have h_p2_prefer_π := (h1 _ _ π π' h_p1_neq_p2).mp h_p1_prefer_π'
  have π_eq_π' := h3 p2 _ _ h_p2_prefer_π' h_p2_prefer_π
  rw [π_eq_π'] at h_p1_not_prefer_π
  exact h_p1_not_prefer_π (h2 p1 π')




/-

A sequential game consisting of:
- a set of players
- a set of game states
- a set of possible actions (assumed the same for all players)
- a map 'turn' that tells whose turn it is from a given state
- a map 'move' that takes an action profile and updates the state
- each player has a preference on state trajectories

Some formalizations assume players take the state history as input for their decision.
For simplicity let's just assume the state variable already contains that information.

-/

class SeqGameStruct (P E A: Type) where
  move: (P → A) → E → E

variable {P E A: Type} [DecidableEq P]

def SeqGameStruct.step (G: SeqGameStruct P E A) (π: P → E → A) (ε: E): E :=
  G.move (fun p => π p ε) ε

def SeqGameStruct.run (G: SeqGameStruct P E A) (ε: E) (π: P → E → A): Nat → E :=
  fun n => match n with
  | Nat.zero => ε
  | Nat.succ prev =>
    let s := run G ε π prev
    G.step π s

class SeqGame (P E A: Type) extends SeqGameStruct P E A where
  prefer: P → Prefer (Nat → E)

def SeqGame.toOutcomeGame (G: SeqGame P E A) (ε: E): OutcomeGame P (E → A) (Nat → E) := {
  play := G.run ε
  prefer := G.prefer
}

def subgame_perfect_equilibrium (G: SeqGame P E A) (π: P → E → A): Prop :=
  ∀ s, nash_equilibrium (G.toOutcomeGame s).toGame π

class SeqUtilityGame (P E A U: Type) extends SeqGameStruct P E A where
  uvalue: P → E → U
  prefer: Prefer U

def hvalue (G: SeqUtilityGame P E A U) (σ: (Nat → U) → U) (p: P) (e: Nat → E): U :=
  σ (fun t => G.uvalue p (e t))

def πvalue (G: SeqUtilityGame P E A U) (σ: (Nat → U) → U) (p: P) (π: P → E → A) (e: E): U :=
  let seq := G.run e π
  hvalue G σ p seq

def SeqUtilityGame.toUtilityGame (G: SeqUtilityGame P E A U) (σ: (Nat → U) → U) (e: E): UtilityGame P (E → A) U := {
  play := fun π => fun p =>
    let seq := G.run e π
    hvalue G σ p seq
  prefer := G.prefer
}

def tail {U: Type} (u: Nat → U): Nat → U :=
  fun t => u (t + 1)

/-

Abstract version of Bellman optimality principle:

Suppose we have a sequential utility game,
equipped with σ (sum-like) and α (addition-like)
such that for any sequence u0, u1, u2, ... of utilities:

σ(u0, u1, u2, ...) = α(u0, σ(u1, u2, ...))

(For standard discounted weighting take α(u, v) = u + βv, for nondiscounted take α(u, v) = u + v.)

Fix a state s, player p, let π0, π1 be profiles.
Let Up(s) be the utility player p associates to state s.
Let s0, s1 be the result of play under π0, π1 after one step starting from s.
Let Vp(s0, π0) and Vp(s1, π1) be the longterm value of states s0 and s1, played under π0 and π1 respectively.

Theorem: if Up(s) + Vp(s0, π0) ≤ Up(s) + Vp(s1, π0) then p prefers π0 ≤ π1 in the underlying normal-form game started from s.

-/

def SeqUtilityGame.NormalForm (G: SeqUtilityGame P E A U) (σ: (Nat → U) → U) (ε: E): Game P (E → A) :=
  (G.toUtilityGame σ ε).toOutcomeGame.toGame

example (G: SeqUtilityGame P E A U)
  (σ: (Nat → U) → U)
  (α: U → U → U)
  (h0: ∀ u: Nat → U, α (u 0) (σ (tail u)) = σ u)
  (ε: E) (p: P) (π0 π1: P → E → A)
  (h1: G.prefer (α (G.uvalue p ε) (πvalue G σ p π0 (G.move (flip π0 ε) ε))) (α (G.uvalue p ε) (πvalue G σ p π1 (G.move (flip π1 ε) ε)))):
  (G.NormalForm σ ε).prefer p π0 π1 := by
  simp_all [SeqUtilityGame.NormalForm, SeqUtilityGame.toUtilityGame, UtilityGame.toOutcomeGame, OutcomeGame.toGame]
  simp_all [πvalue, hvalue]
  rw [←h0]
  rw (config := {occs := .pos [2]}) [←h0]
  simp_all [SeqGameStruct.run]
  -- obnoxious lemma
  have {X Y: Type} {a b c d x: X} {f: X → X → Y} {g: Y → Y → Prop} (h1: g (f x a) (f x b)) (h2: a = c) (h3: b = d): g (f x c) (f x d) := by
    rw [←h2, ←h3]
    exact h1
  apply this h1 <;> (
    congr
    ext t
    simp [tail, SeqGameStruct.run]
    congr
    induction t with
    | zero => simp [SeqGameStruct.run]; rfl
    | succ previous ih => simp [SeqGameStruct.run, ih]
  )

-- Let G be a sequential utility game with a utility aggregator σ.
-- An arbitrary function v: P → E → U is called a valuation if
-- maximizing v always leads to preferable trajectories.
def valuation (G: SeqUtilityGame P E A U) (σ: (Nat → U) → U) (v: P → E → U): Prop :=
  ∀ p s π0 π1, G.prefer (πvalue G σ p π0 s) (πvalue G σ p π1 s) ↔ G.prefer (v p (G.step π0 s)) (v p (G.step π1 s))

example (G: SeqUtilityGame P E A U) (σ: (Nat → U) → U) (v: P → E → U) (hv: valuation G σ v)
(α: U → U → U) (p: P)
  (h0: ∀ u: Nat → U, α (u 0) (σ (tail u)) = σ u):
  ∀ ε, ∀ π, G.prefer (α (G.uvalue p ε) (v p (G.step π ε))) (v p ε) := by
  intro ε π

  exact?
