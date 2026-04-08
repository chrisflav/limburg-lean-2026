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

namespace Playground

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

To make a new definition in `Lean`, we use the `def` keyword. The name `Nilpotent` can be
freely chosen.

What appears on the left of the `:` are the *parameters* of the definition, what is on
the right is the *type* of the definition. Here, we are defining a proposition, i.e.
a statement that can be true or false.
-/

/-- An element `x` of a ring `R` is nilpotent if there exists `n : ℕ` such that `x ^ n = 0`. -/
def Nilpotent (x : R) : Prop :=
  ∃ n : ℕ, x ^ n = 0

/-
## Proving theorems

To prove a theorem, we use the `theorem` keyword. Again, the name `Nilpotent.zero` is
a choice.

Everything on the left of the `:` are the *assumptions* and what is given on the right
is the *conclusion* of the theorem. The proof itself is started with the `by` keyword.

At this point, you should move your cursor to any position in the proof and watch
the info view on the right hand side of the screen. Observe that the infoview
is changing depending on the position of the cursor in the proof.

What follows after the symbol `⊢` is the current *goal* of the proof. At the beginning
of the proof, the goal is equal to the conclusion of the theorem we are proving. At
the end of the proof, the goal vanishes and we are shown `Goals accomplished 🎉` instead,
which signals that the proof is complete.

Everything above the goal is the current *context*: It includes all assumptions, but
also all other variables that are available to us in the current proof.
-/

/-- `0` is nilpotent. -/
@[simp]
theorem Nilpotent.zero : Nilpotent (0 : R) := by
  /-
  Every line in this proof is a *tactic*. Every tactic either modifies the context
  or the goal. The basic procedure of a Lean proof is to apply a sequence
  of tactics that step by step prove the goal.
  -/
  -- Unfold the definition of `Nilpotent` in the goal.
  unfold Nilpotent at ⊢
  -- We have to show an `∃ n, ...`. To say, choose `n = 1`, we use the `use` tactic.
  use 1
  -- Simplify the goal and finish.
  simp

/-- If `x` is nilpotent, also `a * x` is nilpotent for every `a : R`. -/
theorem Nilpotent.mul_left {x : R} (hx : Nilpotent x) (a : R) : Nilpotent (a * x) := by
  -- Unfold the definition of `Nilpotent` in the assumption `hx` and the goal.
  unfold Nilpotent at hx ⊢
  -- Since `hx` is of the form `∃ n, ...`, we obtain a witness `n` and a proof `hn` that
  -- `n` satisfies `...`.
  obtain ⟨n, hn⟩ := hx
  -- Choose `n = n`.
  use n
  -- Rewrite with algebraic identities in the goal to complete the proof.
  rw [mul_pow]
  rw [hn]
  rw [mul_zero]

/-
The following lemma is slightly trickier!
-/

/-- The sum of two nilpotent elements is nilpotent. -/
theorem Nilpotent.add {x y : R} (hx : Nilpotent x) (hy : Nilpotent y) : Nilpotent (x + y) := by
  -- We can also skip the `unfold` step, Lean is happy to unfold it when needed.
  obtain ⟨n, hn⟩ := hx
  obtain ⟨m, hm⟩ := hy
  use n + m
  -- Use the binomial theorem to write `(x + y) ^ (n + m)` as a sum.
  rw [add_pow]
  -- To show `∑ i, xᵢ = 0`, it suffices to show `xᵢ = 0` for every `i`.
  apply Finset.sum_eq_zero
  -- The goal is a `∀ k ∈ _, ...` statement. To prove it, we introduce a variable `k`
  -- and a proof that `k ∈ _`.
  intro k hk
  -- Argue by case distinction if `k ≤ n`:
  by_cases h : k ≤ n
  · -- Introduce an auxiliary fact. Proving it works the same way as proving a theorem.
    have : n + m - k = m + (n - k) := by
      -- Use general purpose automation to close the goal.
      grind
    simp [this, pow_add, hm]
  · have : k = n + (k - n) := by
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
  -- This holds by definition.
  rfl

/-- Any prime ideal `p` contains the nilradical. -/
theorem le_of_isPrime (p : Ideal R) [p.IsPrime] :
    𝒩(R) ≤ p := by
  -- `I ≤ J` for ideals means that the underlying subset of `I` is contained in the
  -- underlying subset of `J`. This is also a statement of the form `∀ x ∈ I, x ∈ J`,
  -- so we can use `intro`:
  intro x hx
  -- Simplify the hypothesis `hx`.
  simp at hx
  obtain ⟨n, hn⟩ := hx
  -- Since `p` is prime, to show that `x ∈ p`, it suffices to show that `x ^ n ∈ p`.
  apply Ideal.IsPrime.mem_of_pow_mem _ n
  · simp [hn]
  · -- Close the goal by applying a hypothesis in the context.
    assumption

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
  -- We have to show two inclusions.
  apply le_antisymm
  · -- To show an ideal is less or equal than an infimum of a set of ideals `𝒯`, it suffices to
    -- show it is `≤` than every ideal in `𝒯`.
    rw [le_sInf_iff]
    intro p hp
    dsimp at hp
    -- Apply the lemma we have shown before.
    apply le_of_isPrime
  · intro x hx
    -- Argue by contrapositive.
    contrapose! hx
    -- Consider the following auxiliary set of ideals in `R`.
    let 𝒮 : Set (Ideal R) :=
      { I | ∀ n : ℕ, x ^ n ∉ I }
    -- By assumption, `𝒮` is non-empty.
    have h0 : 0 ∈ 𝒮 := by
      simp [𝒮]
      grind
    -- By Zorn's lemma, `𝒮` has a maximal element `p`.
    obtain ⟨p, hle, ⟨hmem, hmax⟩⟩ : ∃ p : Ideal R, 0 ≤ p ∧ Maximal (· ∈ 𝒮) p := by
      -- Apply Zorn's lemma
      apply zorn_le_nonempty₀ 𝒮 _ 0 h0
      -- It remains to show the chain condition.
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
    -- We claim it suffices to show that `p` is a prime ideal.
    suffices hp : Ideal.IsPrime p by
      simp
      use p, hp
      rw [← pow_one x]
      apply hmem
    -- Since `p` is maximal in `𝒮`, any ideal strictly larger than `p` is not in `𝒮`.
    -- We use this twice, so let's make it a separate claim.
    have H (y : R) (hy : y ∉ p) : ∃ n, x ^ n ∈ p ⊔ Ideal.span {y} := by
      suffices h : p ⊔ Ideal.span {y} ∉ 𝒮 by
        simp [𝒮] at h
        grind
      by_contra
      have := hmax this le_sup_left
      simp at this
      contradiction
    -- To show that `p` is prime, we have to show it is not the unit ideal and
    -- `r * s ∈ p → r ∈ p ∨ s ∈ p`.
    constructor
    · -- A negation `¬ P` is an implication `P → False`, so we can use `intro`.
      intro h
      -- Substitute `p` everywhere with the RHS of `h`.
      subst h
      have := hmem 1
      simp at this
    · intro r s hrs
      -- We prefer showing the contrapositive: `r ∉ p → s ∉ p → r * s ∉ p`.
      contrapose! hrs
      -- We claim that `p ⊔ span {r * s}` is not contained in `𝒮`.
      have h : p ⊔ Ideal.span {r * s} ∉ 𝒮 := by
        -- By our previous claim `H`, there exist `k` and `m` such that `x ^ n ∈ p ⊔ span {r}
        -- and `x ^ m ∈ p ⊔ span {s}`.
        obtain ⟨k, hk⟩ := H r hrs.1
        obtain ⟨m, hm⟩ := H s hrs.2
        have : (p ⊔ Ideal.span {r}) * (p ⊔ Ideal.span {s}) ≤ p ⊔ Ideal.span {r * s} := by
          grw [Ideal.sup_mul_sup_le_sup_left, Ideal.span_mul_span, Set.singleton_mul_singleton]
        simp [𝒮]
        -- We claim that `x ^ (k + m) ∈ p ⊔ span {r * s}`.
        use k + m
        rw [pow_add]
        apply this
        exact Ideal.mul_mem_mul hk hm
      intro hc
      -- If `r * s ∈ p`, this would contradict `h`, because then `p ⊔ span {r * s} = p ∈ 𝒮`.
      apply h
      convert hmem
      simpa

/-- An element `x` is nilpotent if and only if it is contained in every prime ideal.
This is merely a reformulation of `nilradical_eq_sInf`, but it is easier to use
in practice. -/
lemma nilpotent_iff_mem_of_isPrime {x : R} :
    Nilpotent x ↔ ∀ p : Ideal R, p.IsPrime → x ∈ p := by
  rw [← mem_nilradical_iff, nilradical_eq_sInf]
  simp

end Playground
