variable {X: Type}

def left_identity (op: X → X → X) (id: X): Prop :=
  ∀ x, op id x = x

def right_identity (op: X → X → X) (id: X): Prop :=
  ∀ x, op x id = x

-- fun fact: a right identity is the same as a left identity of the flipped operation
#print flip
theorem right_identity_iff (op: X → X → X) (id: X): right_identity op id ↔ left_identity (flip op) id := by
  rfl

def identity (op: X → X → X) (id: X): Prop :=
  left_identity op id ∧ right_identity op id

-- if id is a left identity and id' is a right identity then id = id'
theorem left_right_identity {op: X → X → X} {id id': X} (h: left_identity op id) (h': right_identity op id'): id = id' := by
  calc
    id = op id id' := by rw [h' id]
     _ = id' := by rw [h id']

-- so it follows that two-sided identities are unique
theorem identity_unique {op: X → X → X} {id id': X} (h: identity op id) (h': identity op id'): id = id' := by
  exact left_right_identity h.left h'.right
