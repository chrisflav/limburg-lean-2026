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
  sorry

/-- If `x` is nilpotent, also `x * a` is nilpotent for any `a`. -/
-- Note that we have already proven that `a * x` is nilpotent.
lemma Nilpotent.mul_right {x : R} (hx : Nilpotent x) (a : R) :
    Nilpotent (x * a) := by
  sorry

/-- If `f : R →+* S` is a ring homomorphism, the image of any nilpotent element is nilpotent. -/
lemma Nilpotent.map {S : Type} [CommRing S] (f : R →+* S) {x : R} (hx : Nilpotent x) :
    Nilpotent (f x) := by
  sorry

/-
To check a lemma from the library, you can use the `#check` command.
Hint: The lemma might be useful for the next exercise.
-/
#check mul_neg_geom_sum

/-- The sum of nilpotent elements is nilpotent. -/
lemma Nilpotent.sum {ι : Type} (s : Finset ι) (x : ι → R) (hx : ∀ i, Nilpotent (x i)) :
    Nilpotent (∑ i ∈ s, x i) := by
  -- Bonus: I give you the skeleton as a head start.
  classical
  induction s using Finset.induction with
  | empty =>
    sorry
  | insert a s ha h =>
    -- Hint: `Finset.sum_insert`
    sorry

/-- If `x` is nilpotent, then `1 + x` is a unit. -/
lemma Nilpotent.isUnit_one_add {x : R} (hx : Nilpotent x) : IsUnit (1 + x) := by
  -- Use `isUnit_iff_exists_inv` to unfold `IsUnit`.
  rw [isUnit_iff_exists_inv]
  -- Hint: Use `mul_neg_geom_sum`. Also a `calc` block could be useful here.
  sorry

/-- If `u` is a unit and `x` is nilpotent, then also `u + x` is nilpotent. -/
lemma Nilpotent.isUnit_add {u : R} (hu : IsUnit u) {x : R} (hx : Nilpotent x) :
    IsUnit (u + x) := by
  sorry

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
  sorry

/-- If `P` is a unit, the constant coefficient is also a unit. -/
lemma Polynomial.isUnit_coeff_zero_of_isUnit {P : R[X]} (h : IsUnit P) :
    IsUnit (P.coeff 0) := by
  -- Hint: `Polynomial.mul_coeff_zero` might be useful.
  sorry

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
  sorry

/-- The final boss: Characterization of when a polynomial is a unit. -/
-- Hint: All hard work is done, you just have to piece together the previous lemmas.
theorem Polynomial.isUnit_iff {P : R[X]} :
    IsUnit P ↔ IsUnit (P.coeff 0) ∧ (∀ i ≠ 0, Nilpotent (P.coeff i)) := by
  sorry

end Playground
