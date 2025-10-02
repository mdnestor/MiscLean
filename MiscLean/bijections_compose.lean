def injection (f: A → B): Prop :=
  ∀ a1 a2: A, f a1 = f a2 → a1 = a2

def surjection (f: A → B): Prop :=
  ∀ b: B, ∃ a: A, f a = b

def bijection (f: A → B): Prop :=
  injection f ∧ surjection f

theorem identity_injection: injection (fun a: A => a) := by
  rw [injection]
  intro _ _ h
  exact h

theorem identity_surjection: surjection (fun a: A => a) := by
  rw [surjection]
  intro a
  exists a

theorem identity_bijection: bijection (fun a: A => a) := by
  rw [bijection]
  apply And.intro
  exact identity_injection
  exact identity_surjection

theorem injections_compose (f: A → B) (g: B → C) (h1: injection f) (h2: injection g): injection (g ∘ f) := by
  rw [injection]
  intros a1 a2 h
  have h3: g (f a1) = g (f a2) := h
  have h4: f a1 = f a2 := h2 (f a1) (f a2) h3
  exact h1 a1 a2 h4

theorem surjections_compose (f: A → B) (g: B → C) (h1: surjection f) (h2: surjection g): surjection (g ∘ f) := by
  rw [surjection]
  intro c
  obtain ⟨b, h3⟩ := h2 c
  obtain ⟨a, h4⟩ := h1 b
  exists a
  simp
  rw [h4, h3]

theorem bijections_compose (f: A → B) (g: B → C) (h1: bijection f) (h2: bijection g): bijection (g ∘ f) := by
  rw [bijection]
  apply And.intro
  apply injections_compose f g h1.1 h2.1
  apply surjections_compose f g h1.2 h2.2
