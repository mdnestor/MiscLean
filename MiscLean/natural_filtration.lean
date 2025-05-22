
import Mathlib.Data.Set.Basic
import Mathlib.Order.SetNotation

variable {T Ω S: Type}

def generate (f: Set (Set Ω) → Prop) (B: Set (Set Ω)): Set (Set Ω) :=
  Set.sInter {F | B ⊆ F ∧ f F}

theorem generate_mono (f: Set (Set Ω) → Prop) (B1 B2: Set (Set Ω)) (h: B1 ⊆ B2): generate f B1 ⊆ generate f B2 := by
  intro A hA
  simp_all [generate]
  intro t h1 h2
  apply hA
  exact fun _ x => h1 (h x)
  exact h2

def pullback (f: X → Y) (G: Set (Set Y)): Set (Set X) :=
  fun A => Set.image f A ∈ G

def natural_filtration [LE T] (X: T → Ω → S) (G: Set (Set S)) (f: Set (Set Ω) → Prop): T → Set (Set Ω) :=
  fun t => generate f (Set.iUnion fun s: {s | s ≤ t} => pullback (X s) G)

theorem natural_filtration_mono [LinearOrder T] (X: T → Ω → S) (G: Set (Set S)) (f: Set (Set Ω) → Prop) (s t: T) (h: s ≤ t): natural_filtration X G f s ⊆ natural_filtration X G f t := by
  apply generate_mono
  intro _ hA
  obtain ⟨_, hi⟩ := hA
  simp_all
  obtain ⟨j, hj⟩ := hi.left
  exists j
  constructor
  exact le_trans hj.left h
  rw [hj.right]
  exact hi.right

