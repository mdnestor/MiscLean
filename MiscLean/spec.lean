-- definition of the Zariski topology and the Spec functor

import Mathlib.Data.Set.Basic
import Mathlib.Order.SetNotation
import Mathlib.Data.Finite.Defs
import Aesop.Main

class CommRing (X: Type u) where
  add: X → X → X
  mul: X → X → X
  zero: X
  one: X
  add_assoc: ∀ x y z: X, add (add x y) z = add x (add y z)
  add_comm: ∀ x y: X, add x y = add y x
  add_zero: ∀ x: X, add x zero = x
  zero_add: ∀ x: X, add zero x = x
  inv: X → X
  add_inv_left: ∀ x: X, add (inv x) x = zero
  add_inv_right: ∀ x: X, add x (inv x) = zero
  mul_assoc: ∀ x y z: X, mul (mul x y) z = mul x (mul y z)
  mul_one: ∀ x: X, mul x one = x
  one_mul: ∀ x: X, mul one x = x
  mul_comm: ∀ x y: X, mul x y = mul y x
  left_distrib: ∀ x y z: X, mul x (add y z) = add (mul x y) (mul x z)
  right_distrib: ∀ x y z: X, mul (add x y) z = add (mul x z) (mul y z)

open CommRing

lemma zero_mul {X: Type u} [CommRing X] (x: X): mul zero x = zero := by
  calc
    mul zero x = add (mul zero x) zero := by rw [add_zero]
             _ = add (mul zero x) (add (mul zero x) (inv (mul zero x))) := by rw [add_inv_right]
             _ = add (add (mul zero x) (mul zero x)) (inv (mul zero x)) := by rw [add_assoc]
             _ = add (mul (add zero zero) x) (inv (mul zero x)) := by rw [right_distrib]
             _ = add (mul zero x) (inv (mul zero x)) := by rw [add_zero]
             _ = zero := by rw [add_inv_right]

class Ideal {X: Type u} [CommRing X] (I: Set X): Prop where
  h1: zero ∈ I
  h2: ∀ x y: X, x ∈ I → y ∈ I → add x y ∈ I
  h3: ∀ x y: X, x ∈ I → mul x y ∈ I

class PrimeIdeal {X: Type u} [CommRing X] (I: Set X) extends Ideal I: Prop where
  h4: ∀ x y: X, mul x y ∈ I → x ∈ I ∨ y ∈ I
  h5: I ⊂ Set.univ

def Ideals (X: Type u) [CommRing X]: Set (Set X) :=
  fun I => Ideal I

def PrimeIdeals (X: Type u) [CommRing X]: Set (Set X) :=
  fun I => PrimeIdeal I

class TopologicalSpace (X: Type u) where
  opensets: Set (Set X)
  empty_isOpen: ∅ ∈ opensets
  univ_isOpen: Set.univ ∈ opensets
  union_isOpen: ∀ S: Set (Set X), S ⊆ opensets → Set.sUnion S ∈ opensets
  inter_isOpen: ∀ S: Set (Set X), S ⊆ opensets ∧ Finite S → Set.sInter S ∈ opensets

def V {X: Type u} [CommRing X] (I: Set X): Set (PrimeIdeals X) :=
  fun ⟨P, _⟩ => I ⊆ P

theorem univ_ideal {X: Type u} [CommRing X]: Ideal (@Set.univ X) := {
  h1 := by simp
  h2 := by simp
  h3 := by simp
}

-- V(X) = ∅ 
theorem V_univ {X: Type u} [CommRing X]: V (@Set.univ X) = ∅ := by
  ext ⟨_, hP⟩
  constructor
  . intro
    simp_all
    have := hP.h5.right
    contradiction
  . intro
    simp_all

-- V({0}) = PrimeIdeals(X)
theorem V_zero {X: Type u} [CommRing X]: V (Set.singleton (zero: X)) = Set.univ := by
  ext P
  constructor
  intro
  simp
  simp
  intro _ hx
  rw [Set.eq_of_mem_singleton hx]
  exact P.2.h1

theorem V_union {X: Type u} [CommRing X] (I: Set (Set X)): V (Set.sUnion I) = Set.sInter (Set.image V Set.univ) := by
  ext P
  constructor
  intro h S hS
  obtain ⟨a, ha⟩ := hS
  simp at ha
  rw [←ha]
  intro x hx

  simp

  simp
  simp
  intro _ hx
  rw [Set.eq_of_mem_singleton hx]
  exact P.2.h1


def Spectrum {X: Type u} [CommRing X]: TopologicalSpace (PrimeIdeals X) := {
  opensets := Set.image (fun I => (V I)ᶜ) (Ideals X)
  empty_isOpen := by
    exists {zero}
    constructor
    . constructor
      simp
      intros
      simp_all
      apply add_zero
      intro _ y _
      simp_all
      rw [zero_mul]
    . simp
      exact V_zero
  univ_isOpen := by
    exists Set.univ
    constructor
    exact univ_ideal
    simp
    rw [V_univ]
  union_isOpen := by
    intro S h
    simp
    simp [Set.image] at h
    let f: S → Ideals X := by
      intro s
      have h1 := h s.prop
      simp at h1
      let y := Classical.choose h1
      have hy := Classical.choose_spec h1
      exact ⟨y, hy.left⟩
    let Is := Set.image f Set.univ
    -- ∃ x ∈ Ideals X, (V x)ᶜ = ⋃₀ S
    sorry
  inter_isOpen := by
    intro S h
    simp
    -- ∃ x ∈ Ideals X, (V x)ᶜ = ⋂₀ S
    sorry
}
