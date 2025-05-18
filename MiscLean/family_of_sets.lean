/-

Results about set families

-/

import Mathlib.Data.Set.Basic
import Mathlib.Order.SetNotation

def family_respecting {X Y: Type} (F: Set (Set X)) (G: Set (Set Y)) (f: X → Y): Prop :=
  ∀ B ∈ G, Set.preimage f B ∈ F

example {X Y Z: Type} (f: X → Y) (g: Y → Z) (B: Set Z): Set.preimage (g ∘ f) B = ((Set.preimage f) ∘ (Set.preimage g)) B := by
  exact rfl

theorem family_respecting.comp {X Y Z: Type} {F: Set (Set X)} {G: Set (Set Y)} {H: Set (Set Z)} {f: X → Y} {g: Y → Z} (hf: family_respecting F G f) (hg: family_respecting G H g): family_respecting F H (g ∘ f) := by
  intro B hB
  exact hf (g ⁻¹' B) (hg B hB)

def family_pushforward {X Y: Type} (F: Set (Set X)) (f: X → Y): Set (Set Y) :=
  {B | Set.preimage f B ∈ F}

def family_pullback {X Y: Type} (G: Set (Set Y)) (f: X → Y): Set (Set X) :=
  {A | Set.image f A ∈ G}

def generate {X: Type} (f: Set (Set X) → Prop) (B: Set (Set X)): Set (Set X) :=
  Set.sInter {F | B ⊆ F ∧ f F}

-- if the family is closed under arbitrary intersections, then the generated family is indeed a family
theorem generate_sound {X: Type} {f: Set (Set X) → Prop} (hf: ∀ C: Set (Set (Set X)), (∀ F ∈ C, f F) → f (Set.sInter C)) (B: Set (Set X)): f (generate f B) := by
  apply hf
  intro _ hF
  exact hF.right

theorem generate_basis_mem {X: Type} (f: Set (Set X) → Prop) (B: Set (Set X)): B ⊆ generate f B := by
  intro _ hA
  simp[generate]
  intro _ hC1 _
  exact hC1 hA

theorem generate_least {X: Type} {f: Set (Set X) → Prop} {B: Set (Set X)} {F: Set (Set X)} (h1: f F) (h2: B ⊆ F): generate f B ⊆ F := by
  intro _ hA
  have: ⋂₀ {F | B ⊆ F ∧ f F} ⊆ F := by intro; simp_all
  exact this hA

theorem generate_mono {X: Type} (f: Set (Set X) → Prop) {B1 B2: Set (Set X)} (h: B1 ⊆ B2): generate f B1 ⊆ generate f B2 := by
  intro A hA
  simp_all [generate]
  intro B hB1 hB2
  apply hA
  exact le_trans h hB1
  exact hB2
