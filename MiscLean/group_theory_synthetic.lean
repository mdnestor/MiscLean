-- experiment with synthetic group theory
axiom Group: Type

axiom Homo (A B: Group): Type
axiom Homo.id (A: Group): Homo A A

axiom Homo.compose {A B C: Group} (a: Homo A B) (b: Homo B C): Homo A C
infix:0 ">" => Homo.compose

axiom Homo.assoc {A B C D: Group} (a: Homo A B) (b: Homo B C) (c: Homo C D): (a > (b > c)) = ((a > b) > c)
axiom Homo.compose_id_left {A B: Group} (a: Homo A B): ((Homo.id A) > a) = a
axiom Homo.compose_id_right {A B: Group} (a: Homo A B): (a > (Homo.id B)) = a

def mono {A B: Group} (a: Homo A B): Prop := ∀ Z: Group, ∀ z1 z2: Homo Z A, (z1 > a) = (z2 > a) → (z1 = z2)
def epi {A B: Group} (a: Homo A B): Prop := ∀ C: Group, ∀ b1 b2: Homo B C, (a > b1) = (a > b2) → (b1 = b2)
def iso {A B: Group} (a: Homo A B): Prop := mono a ∧ epi a

def isomorphic (A B: Group): Prop := ∃ a: Homo A B, iso a

/- strictify :3 -/
axiom eq_iff_iso (A B: Group): A = B ↔ isomorphic A B

axiom Homo.zero (A B: Group): Homo A B
axiom Zero: Group
axiom Zero.in (A: Group) (a: Homo A Zero): a = Homo.zero A Zero
axiom Zero.out (A: Group) (a: Homo Zero A): a = Homo.zero Zero A

example (A: Group): epi (Homo.zero A Zero) := sorry
example (A: Group): mono (Homo.zero Zero A) := sorry

def subgroup (A B: Group): Prop := ∃ f: Homo A B, mono f

axiom kernel {A B: Group} (a: Homo A B): Group
axiom image {A B: Group} (a: Homo A B): Group

axiom kernel_subgroup (A B: Group) (a: Homo A B): subgroup (kernel a) A
axiom image_subgroup (A B: Group) (a: Homo A B): subgroup (image a) B

def normal_subgroup (A B: Group): Prop := (subgroup A B) ∧ (∃ C: Group, ∃ a: Homo B C, kernel a = A)

def lemma1 {A B C: Group} (a: Homo A B) (b: Homo B C): mono a → kernel (a > b) = kernel b := sorry

example {A B C: Group} (h1: subgroup A B) (h2: subgroup B C) (h3: normal_subgroup A C): normal_subgroup A B := by
  sorry /- apply lemma1 -/
