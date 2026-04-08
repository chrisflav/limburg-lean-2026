/-
Copyright (c) 2026 Christian Merten. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Merten
-/
import Mathlib

/-!
# Exercises on nilpotent elements

The goal of this series of exercises is to show that if `P` is a polynomial
in one variable, then `P` is a unit if and only if the constant coefficient
is a unit and all other coefficients are nilpotent.
-/

-- This enables the notation `R[X]` for the polynomial ring in one variable.
open Polynomial

namespace ExercisePlayground

variable {R : Type} [CommRing R]

section AlreadyCovered

/-- An element `x` of a ring `R` is nilpotent if there exists `n : ℕ` such that `x ^ n = 0`. -/
def Nilpotent (x : R) : Prop :=
  ∃ n : ℕ, x ^ n = 0

/-- `0` is nilpotent. -/
@[simp]
theorem Nilpotent.zero : Nilpotent (0 : R) := by
  use 1
  simp

/-- If `x` is nilpotent, also `a * x` is nilpotent for every `a : R`. -/
theorem Nilpotent.mul_left {x : R} (hx : Nilpotent x) (a : R) : Nilpotent (a * x) := by
  obtain ⟨n, hn⟩ := hx
  use n
  simp [mul_pow, hn]

/-- The sum of two nilpotent elements is nilpotent. -/
theorem Nilpotent.add {x y : R} (hx : Nilpotent x) (hy : Nilpotent y) : Nilpotent (x + y) := by
  obtain ⟨n, hn⟩ := hx
  obtain ⟨m, hm⟩ := hy
  use n + m
  rw [add_pow]
  apply Finset.sum_eq_zero
  intro k hk
  by_cases h : k ≤ n
  · have : n + m - k = m + (n - k) := by grind
    simp [this, pow_add, hm]
  · have : k = n + (k - n) := by grind
    rw [this, pow_add, hn]
    simp

variable (R) in
/-- The set of nilpotent elements forms an ideal: The nilradical of `R`. -/
def nilradical : Ideal R where
  carrier := { x | Nilpotent x }
  zero_mem' := by simp
  add_mem' {x y} hx hy := Nilpotent.add hx hy
  smul_mem' a _ hx := Nilpotent.mul_left hx a

-- Lean's syntax is extensible: Let us introduce a notation `𝒩(R)` for the nilradical.
notation3 "𝒩(" R ")" => nilradical R

-- We can extend Lean's automation by declaring a theorem as a simplification rule.
-- This means it will later be used by `simp` and `grind`.
@[simp, grind =]
theorem mem_nilradical_iff (x : R) : x ∈ 𝒩(R) ↔ Nilpotent x := by
  rfl

/-- Any prime ideal `p` contains the nilradical. -/
theorem le_of_isPrime (p : Ideal R) [p.IsPrime] :
    𝒩(R) ≤ p := by
  intro x hx
  obtain ⟨n, hn⟩ := hx
  exact Ideal.IsPrime.mem_of_pow_mem ‹_› n (by simp [hn])

/-
The following two lemmas will be useful in the next proof, let's ignore them for now.
-/

theorem Ideal.sup_mul_sup_le_sup_left (I J K : Ideal R) : (I ⊔ J) * (I ⊔ K) ≤ I ⊔ J * K := by
  rw [Ideal.sup_mul, sup_le_iff]
  refine ⟨le_trans Ideal.mul_le_right le_sup_left, ?_⟩
  rw [Ideal.mul_sup]
  exact sup_le_sup Ideal.mul_le_left le_rfl

theorem Ideal.sup_mul_sup_le_sup_right (I J K : Ideal R) : (J ⊔ I) * (K ⊔ I) ≤ J * K ⊔ I := by
  grw [sup_comm J I, sup_comm K I, Ideal.sup_mul_sup_le_sup_left, sup_comm]

attribute [grind] Nilpotent

/-- The nilradical of `R` is the intersection of all prime ideals of `R`. -/
theorem nilradical_eq_sInf :
    𝒩(R) = sInf { p : Ideal R | p.IsPrime } := by
  apply le_antisymm
  · rw [le_sInf_iff]
    intro p hp
    dsimp at hp
    apply le_of_isPrime
  · intro x hx
    contrapose! hx
    let 𝒮 : Set (Ideal R) :=
      { I | ∀ n : ℕ, x ^ n ∉ I }
    have h0 : 0 ∈ 𝒮 := by
      simp [𝒮]
      grind
    obtain ⟨p, hle, ⟨hmem, hmax⟩⟩ : ∃ p : Ideal R, 0 ≤ p ∧ Maximal (· ∈ 𝒮) p := by
      apply zorn_le_nonempty₀ 𝒮 _ 0 h0
      intro c hc hchain y hy
      use sSup c
      constructor
      · intro n
        rw [Submodule.mem_sSup_of_directed]
        · simp only [not_exists, not_and]
          tauto
        · use y
        · exact IsChain.directedOn hchain
      · intro z hz
        exact le_sSup hz
    suffices hp : Ideal.IsPrime p by
      simp only [Submodule.mem_sInf, Set.mem_setOf_eq, not_forall]
      use p, hp
      rw [← pow_one x]
      apply hmem
    have H (y : R) (hy : y ∉ p) : ∃ n, x ^ n ∈ p ⊔ Ideal.span {y} := by
      suffices h : p ⊔ Ideal.span {y} ∉ 𝒮 by
        simp [𝒮] at h
        grind
      by_contra
      have := hmax this le_sup_left
      simp at this
      contradiction
    constructor
    · intro rfl
      simpa using hmem 1
    · intro r s hrs
      contrapose! hrs
      have h : p ⊔ Ideal.span {r * s} ∉ 𝒮 := by
        obtain ⟨k, hk⟩ := H r hrs.1
        obtain ⟨m, hm⟩ := H s hrs.2
        have : (p ⊔ Ideal.span {r}) * (p ⊔ Ideal.span {s}) ≤ p ⊔ Ideal.span {r * s} := by
          grw [Ideal.sup_mul_sup_le_sup_left, Ideal.span_mul_span, Set.singleton_mul_singleton]
        simp [𝒮]
        use k + m
        rw [pow_add]
        apply this
        exact Ideal.mul_mem_mul hk hm
      intro hc
      apply h
      convert hmem
      simpa

/-- An element `x` is nilpotent if and only if it is contained in every prime ideal. -/
lemma nilpotent_iff_mem_of_isPrime {x : R} :
    Nilpotent x ↔ ∀ p : Ideal R, p.IsPrime → x ∈ p := by
  rw [← mem_nilradical_iff, nilradical_eq_sInf]
  simp

end AlreadyCovered

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

end ExercisePlayground
