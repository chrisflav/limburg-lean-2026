/-
Copyright (c) 2026 Christian Merten. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Merten
-/
import Limburg.Lectures.Nilradical

/-!
# Exercises on nilpotent elements

The goal of this series of exercises is to show that if `P` is a polynomial
in one variable, then `P` is a unit if and only if the constant coefficient
is a unit and all other coefficients are nilpotent.
-/

-- This enables the notation `R[X]` for the polynomial ring in one variable.
open Polynomial

namespace Playground

variable {R : Type} [CommRing R]

/-- If `x` is nilpotent, also `-x` is nilpotent. -/
lemma Nilpotent.neg {x : R} (hx : Nilpotent x) : Nilpotent (-x) :=
  (nilradical R).neg_mem hx

/-- If `x` is nilpotent, also `x * a` is nilpotent for any `a`. -/
-- Note that we have already proven that `a * x` is nilpotent.
lemma Nilpotent.mul_right {x : R} (hx : Nilpotent x) (a : R) :
    Nilpotent (x * a) := by
  rw [mul_comm]
  apply hx.mul_left

/-- If `f : R →+* S` is a ring homomorphism, the image of any nilpotent element is nilpotent. -/
lemma Nilpotent.map {S : Type} [CommRing S] (f : R →+* S) {x : R} (hx : Nilpotent x) :
    Nilpotent (f x) := by
  obtain ⟨n, hn⟩ := hx
  use n
  rw [← map_pow, hn, map_zero]

/-
To check a lemma from the library, you can use the `#check` command.
Hint: The lemma might be useful for the next exercise.
-/
#check mul_neg_geom_sum

/-- The sum of nilpotent elements is nilpotent. -/
lemma Nilpotent.sum {ι : Type} (s : Finset ι) (x : ι → R) (hx : ∀ i, Nilpotent (x i)) :
    Nilpotent (∑ i ∈ s, x i) := by
  classical
  induction s using Finset.induction with
  | empty => simp
  | insert a s ha h =>
    -- Hint: `Finset.sum_insert`
    rw [Finset.sum_insert ha]
    apply Nilpotent.add (hx a) h

/-- If `x` is nilpotent, then `1 + x` is a unit. -/
lemma Nilpotent.isUnit_one_add {x : R} (hx : Nilpotent x) : IsUnit (1 + x) := by
  -- Use `isUnit_iff_exists_inv` to unfold `IsUnit`.
  rw [isUnit_iff_exists_inv]
  -- Hint: Use `mul_neg_geom_sum`. Also a `calc` block could be useful here.
  obtain ⟨n, hn⟩ := hx
  use ∑ i ∈ Finset.range n, (-x) ^ i
  calc
    (1 + x) * ∑ i ∈ Finset.range n, (-x) ^ i = (1 - (-x)) * ∑ i ∈ Finset.range n, (-x) ^ i := by
      simp
    _ = 1 - (-x) ^ n := by
      rw [mul_neg_geom_sum]
    _ = 1 := by simp; rw [neg_pow]; simp [hn]

/-- If `u` is a unit and `x` is nilpotent, then also `u + x` is nilpotent. -/
lemma Nilpotent.isUnit_add {u : R} (hu : IsUnit u) {x : R} (hx : Nilpotent x) :
    IsUnit (u + x) := by
  rw [isUnit_iff_exists_inv] at hu ⊢
  obtain ⟨b, hb⟩ := hu
  have : IsUnit (1 + b * x) := by
    apply Nilpotent.isUnit_one_add
    apply hx.mul_left
  rw [isUnit_iff_exists_inv] at this
  obtain ⟨c, hc⟩ := this
  use b * c
  nth_rw 1 [← hb] at hc
  rw [← hc]
  ring

/--
A polynomial `P` is a unit if the constant coefficient is a unit and all other
coefficients are nilpotent.
The converse also holds as the next two exercises show.
-/
lemma Polynomial.isUnit_of_isUnit_coeff (P : R[X]) (hunit : IsUnit (P.coeff 0))
    (hnil : ∀ i ≠ 0, Nilpotent (P.coeff i)) :
    IsUnit P := by
  -- Hint: Use `Polynomial.as_sum_range_C_mul_X_pow P`. Also `Finset.range_add_one'` could
  -- be useful.
  rw [Polynomial.as_sum_range_C_mul_X_pow P]
  rw [Finset.range_add_one']
  simp
  apply Nilpotent.isUnit_add
  · simp
    apply hunit
  · apply Nilpotent.sum
    intro i
    apply Nilpotent.mul_right
    apply Nilpotent.map
    apply hnil
    simp

/-- If `P` is a unit, the constant coefficient is also a unit. -/
lemma Polynomial.isUnit_coeff_zero_of_isUnit {P : R[X]} (h : IsUnit P) :
    IsUnit (P.coeff 0) := by
  -- Hint: `Polynomial.mul_coeff_zero` might be useful.
  rw [isUnit_iff_exists_inv] at h ⊢
  obtain ⟨Q, hQ⟩ := h
  use Q.coeff 0
  rw [← Polynomial.mul_coeff_zero, hQ]
  simp

/-- If `P` is a unit, all non-zero coefficients are nilpotent. -/
lemma Polynomial.nilpotent_coeff_of_isUnit {P : R[X]} (h : IsUnit P) {i : ℕ} (hi : i ≠ 0) :
    Nilpotent (P.coeff i) := by
  /-
  Hint: Use `nilpotent_iff_mem_of_isPrime` and use the fact that `R ⧸ p` is a domain
  for a prime ideal `p`.
  Other useful declarations:
  - `Polynomial.mapRingHom` and `Ideal.Quotient.mk` to construct the map `R[X] → (R ⧸ p)[X]`.
  - `Polynomial.degree_eq_zero_of_isUnit` (this requires the ring to be a domain!)
  - `Polynomial.coeff_eq_zero_of_degree_lt`
  - `RingHom.mem_ker` and `Ideal.Quotient.mk_ker`
  -/
  rw [nilpotent_iff_mem_of_isPrime]
  intro p hp
  let f := Polynomial.mapRingHom (Ideal.Quotient.mk p)
  have : (f P).degree = 0 := by
    apply Polynomial.degree_eq_zero_of_isUnit
    apply IsUnit.map
    exact h
  have : (f P).coeff i = 0 := by
    apply coeff_eq_zero_of_degree_lt
    rw [this]
    simp
    grind
  simp [f, ← RingHom.mem_ker] at this
  exact this

/-- The final boss: Characterization of when a polynomial is a unit. -/
-- Hint: All hard work is done, you just have to piece together the previous lemmas.
theorem Polynomial.isUnit_iff {P : R[X]} :
    IsUnit P ↔ IsUnit (P.coeff 0) ∧ (∀ i ≠ 0, Nilpotent (P.coeff i)) := by
  constructor
  · intro h
    constructor
    · apply isUnit_coeff_zero_of_isUnit
      exact h
    · apply nilpotent_coeff_of_isUnit
      exact h
  · intro h
    apply isUnit_of_isUnit_coeff
    · exact h.1
    · exact h.2

end Playground
