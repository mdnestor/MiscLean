/-
Harary (1953) proved the following theorem:
Let G be a simple undirected graph (every pair of nodes is either connected or not).
Denote x ~ y if x is connected to y and x ≁ y otherwise.
Note that for every 3 nodes x, y, z, there can be either 0, 1, 2, or 3 edges between them in total.
Call x, y, z "locally balanced" if the total number of edges between them is either 1 or 3.
Define G to be (globally) balanced if every 3 nodes are locally balanced. 
Define G to be bipartite complete if it can be partitioned into two complete subgraphs which share no edges.
Equivalently, G is bipartite complete if there exists a function f: G → Bool such that x ∼ y iff. f(x) = f(y). 

Balance theorem: G is balanced ↔ G is bipartite complete.

Proof: First, assume G is bipartite complete.
We want to show G is balanced.
Let x, y, and z be any 3 nodes, and it suffices to show x, y, z are locally balanced.
Case 1. x ~ y and x ~ z. Then bipartite complete implies y ~ z implies locally balanced.
Case 2. x ~ y and x ≁ z. Then bipartite complete implies y ≁ z implies locally balanced.
Case 3. x ≁ y and x ~ z. Then bipartite complete implies y ≁ z implies locally balanced.
Case 4. x ≁ y and x ≁ z. Then bipartite complete implies y ~ z implies locally balanced.
In each case x, y, z are locally balanced, so G is balanced.

Next, assume G is balanced.
We want to show G is bipartite complete.
Let x be an arbitrary node, let A be the set of neighbors of x and let B = G - A.
We will show G is bipartite complete by showing the following hold:
Case 1. y ∈ A and z ∈ A implies (x ∼ y) ∧ (x ∼ z) implies (y ∼ z). 
Case 2. y ∈ A and z ∈ B implies (x ∼ y) ∧ (x ≁ z) implies (y ≁ z).
Case 3. y ∈ B and z ∈ B implies (x ≁ y) ∧ (x ≁ z) implies (y ∼ z).
Therefore G is bipartite complete.

References:
1 "On the notion of balance of a signed graph" by Frank Harary (1953): https://doi.org/10.1307/MMJ%2F1028989917
2 "Networks, Crowds, and Markets: Reasoning about a Highly Connected World" by David Easley and Jon Kleinberg (2010), section 5.2: https://www.cs.cornell.edu/home/kleinber/networks-book/networks-book-ch05.pdf
3 "Signed graph" on Wikipedia: https://en.wikipedia.org/wiki/Signed_graph
4 "Balance theory" on Wikipedia: https://en.wikipedia.org/wiki/Balance_theory
5 "Network Mathematics and Rival Factions" by PBS Infinite Series (2017): https://www.youtube.com/watch?v=qEKNFOaGQcc
-/

structure Graph where
  node: Type
  edge: node → node → Bool
  symmetric: ∀ x y: node, edge x y ↔ edge y x

def three_complete {G: Graph} (x y z: G.node): Prop :=
  G.edge x y ∧ G.edge y z ∧ G.edge x z

def two_connected {G: Graph} (x y z: G.node): Prop :=
  (  G.edge x y ∧ ¬ G.edge y z ∧ ¬ G.edge x z) ∨ /- x y alliance excluding z -/
  (¬ G.edge x y ∧   G.edge y z ∧ ¬ G.edge x z) ∨ /- y z alliance excluding x -/
  (¬ G.edge x y ∧ ¬ G.edge y z ∧   G.edge x z)   /- x z alliance excluding y -/

def locally_balanced {G: Graph} (x y z: G.node): Prop :=
  three_complete x y z ∨ two_connected x y z

def balanced (G: Graph): Prop :=
  ∀ x y z: G.node, locally_balanced x y z

def bipartite_complete (G: Graph): Prop :=
  ∃ f: G.node → Bool, ∀ x y: G.node, G.edge x y ↔ f x = f y

theorem lemma1 {a: Bool} (h: ¬a = true): ¬true = a :=
  fun ha => h ha.symm

theorem lemma2 {a: Bool} (h: ¬a = true): a = false :=
  match a, h with
  | true, h => False.elim (h rfl)
  | false, _ => rfl

theorem lemma3 {a b: Bool} (h1: ¬a = true) (h2: ¬b = true): a = b :=
  match a, b, lemma2 h1, lemma2 h2 with
  | _, _, rfl, rfl => rfl

theorem BipartiteCompleteImpliesBalanced (G: Graph): bipartite_complete G → balanced G := by
  intro h
  rw [balanced]
  intro x y z
  rw [locally_balanced]
  cases h with
  | intro f hf => {
    by_cases hx: f x
    by_cases hy: f y
    by_cases hz: f z
    apply Or.inl
    rw [three_complete, hf, hf, hf, hx, hy, hz]
    simp
    apply Or.inr
    rw [two_connected, hf, hf, hf, hx, hy]
    simp
    exact lemma1 hz
    by_cases hz: f z
    apply Or.inr
    rw [two_connected, hf, hf, hf, hx, hz]
    simp
    exact ⟨lemma1 hy, lemma2 hy⟩
    apply Or.inr
    rw [two_connected, hf, hf, hf, hx]
    apply Or.inr
    apply Or.inl
    exact ⟨lemma1 hy, lemma3 hy hz, lemma1 hz⟩
    by_cases hy: f y
    by_cases hz: f z
    apply Or.inr
    rw [two_connected, hf, hf, hf, hy, hz]
    simp
    exact lemma2 hx
    apply Or.inr
    rw [two_connected, hf, hf, hf, hy]
    simp
    apply Or.inr
    apply Or.inr
    exact ⟨lemma2 hx, lemma1 hz, lemma3 hx hz⟩
    by_cases hz: f z
    apply Or.inr
    rw [two_connected, hf, hf, hf, hz]
    simp
    apply Or.inl
    exact ⟨lemma3 hx hy, lemma2 hy, lemma2 hx⟩
    apply Or.inl
    rw [three_complete, hf, hf, hf]
    exact ⟨lemma3 hx hy, lemma3 hy hz, lemma3 hx hz⟩
  }

theorem BalancedImpliesBipartiteComplete (G: Graph): balanced G → bipartite_complete G := by
  intro h
  rw [bipartite_complete]
  have x: G.node := sorry
  have f: G.node → Bool := fun x' => G.edge x x'
  have hf (x': G.node): f x = f x' ↔ G.edge x x' := sorry
  exists f
  intro y z
  have hb: locally_balanced x y z := by apply h
  apply Iff.intro
  intro hyz
  by_cases hy: f y
  rw [hy]
  sorry
  sorry
  intro hyz
  sorry

theorem BalanceTheorem (G: Graph): balanced G ↔ bipartite_complete G := by
  apply Iff.intro
  exact BalancedImpliesBipartiteComplete G
  exact BipartiteCompleteImpliesBalanced G
