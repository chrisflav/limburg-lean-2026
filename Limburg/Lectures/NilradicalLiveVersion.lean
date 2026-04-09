/-
Copyright (c) 2026 Christian Merten. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Merten
-/
import Mathlib

/-!
# Introduction: A sample of Lean

This file is a gentle introduction to formalising mathematics in Lean. For this, we
define the nilradical of a ring and show that it equals the intersection of all prime ideals.

The reader is expected to open this file in an editor, for example in Visual Studio Code
or on https://live.lean-lang.org/.
-/

namespace LivePlayground

/-
Lean is based on type theory. For the sake of this introduction, it is sufficient to
pretend that `Type` means `Set`.

The main notational difference is: We write `n : ℕ` instead of `n ∈ ℕ`.
-/

/- We fix a type (or set if you prefer) `R` and assume it is endowed with the structure
of a commutative ring. -/
variable {R : Type} [CommRing R]

/-
## Making definitions
-/

/-- An element `x` of a ring `R` is nilpotent if there exists `n : ℕ` such that `x ^ n = 0`. -/
def Nilpotent (x : R) : Prop :=
  ∃ n : ℕ, x ^ n = 0

/-
## Proving theorems
-/

/-- `0` is nilpotent. -/
@[simp]
theorem Nilpotent.zero : Nilpotent (0 : R) := by
  /-
  Every line in this proof is a *tactic*. Every tactic either modifies the context
  or the goal. The basic procedure of a Lean proof is to apply a sequence
  of tactics that step by step prove the goal.
  -/
  unfold Nilpotent
  use 1
  simp only [pow_one]

/-- If `x` is nilpotent, also `a * x` is nilpotent for every `a : R`. -/
theorem Nilpotent.mul_left {x : R} (hx : Nilpotent x) (a : R) : Nilpotent (a * x) := by
  unfold Nilpotent
  unfold Nilpotent at hx
  obtain ⟨n, hn⟩ := hx
  use n
  rw [mul_pow]
  rw [hn]
  simp

/-
The following lemma is slightly trickier!
-/

/-- The sum of two nilpotent elements is nilpotent. -/
theorem Nilpotent.add {x y : R} (hx : Nilpotent x) (hy : Nilpotent y) : Nilpotent (x + y) := by
  unfold Nilpotent at hx hy ⊢
  obtain ⟨n, hn⟩ := hx
  obtain ⟨m, hm⟩ := hy
  use n + m
  nth_rw 1 [add_pow]
  apply Finset.sum_eq_zero
  intro i hi
  by_cases hasdf : i ≤ n
  · have : n + m - i = m + (n - i) := by
      grind
    rw [this, pow_add, hm]
    ring
  · have : i = n + (i - n) := by
      grind
    rw [this, pow_add, hn]
    simp

/-
Now we want to package everything up: The set of nilpotent elements of `R` forms
an ideal of `R`.

The type `Ideal R` is defined as a `structure` with four fields, which is a fancy way of saying
it is defined as a 4-tuple `(s, h_add, h_zero, h_smul)`:
- an underlying subset `s : Set R`
- a proof that `0 ∈ s`
- a proof that `s` is stable under addition: `x ∈ s → y ∈ s → x + y ∈ s`
- a proof that `s` is closed under left multiplication: `∀ a : R, x ∈ s → a * x ∈ s`

To specify an ideal, we use the `where` syntax and provide these four fields.
-/

variable (R) in
/-- The set of nilpotent elements forms an ideal: The nilradical of `R`. -/
def nilradical : Ideal R where
  carrier := { x : R | Nilpotent x }
  add_mem' := by
    intro a b ha hb
    simp
    simp at ha
    simp at hb
    apply Nilpotent.add
    · apply ha
    · apply hb
  zero_mem' := by
    apply Nilpotent.zero
  smul_mem' := by
    intro c x hx
    simp
    have := Nilpotent.mul_left hx c
    apply this

-- Lean's syntax is extensible: Let us introduce a notation `𝒩(R)` for the nilradical.
notation3 "𝒩(" R ")" => nilradical R

-- We can extend Lean's automation by declaring a theorem as a simplification rule.
-- This means it will later be used by `simp` and `grind`.
@[simp, grind =]
theorem mem_nilradical_iff (x : R) : x ∈ 𝒩(R) ↔ Nilpotent x := by
  constructor
  · intro hx
    apply hx
  · intro hx
    apply hx

/-- Any prime ideal `p` contains the nilradical. -/
theorem le_of_isPrime (p : Ideal R) [p.IsPrime] :
    𝒩(R) ≤ p := by
  -- `I ≤ J` for ideals means that the underlying subset of `I` is contained in the
  -- underlying subset of `J`. This is also a statement of the form `∀ x ∈ I, x ∈ J`,
  -- so we can use `intro`:
  sorry

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

-- Let's tell `grind` that it may unfold the definition of `Nilpotent`.
attribute [grind] Nilpotent

/-
The endboss of this file:
-/

/-- The nilradical of `R` is the intersection of all prime ideals of `R`. -/
theorem nilradical_eq_sInf :
    𝒩(R) = sInf { p : Ideal R | p.IsPrime } := by
  sorry

/-- An element `x` is nilpotent if and only if it is contained in every prime ideal.
This is merely a reformulation of `nilradical_eq_sInf`, but it is easier to use
in practice. -/
lemma nilpotent_iff_mem_of_isPrime {x : R} :
    Nilpotent x ↔ ∀ p : Ideal R, p.IsPrime → x ∈ p := by
  rw [← mem_nilradical_iff, nilradical_eq_sInf]
  simp

end LivePlayground
