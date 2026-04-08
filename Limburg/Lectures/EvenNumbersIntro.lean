/-
Copyright (c) 2025 Christian Merten. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Merten
-/
import Mathlib

/-!
# Introduction

## References

Some of the examples are taken from

- Patrick Massot et al.: Glimpse of Lean
  (https://github.com/PatrickMassot/GlimpseOfLean)
-/

namespace Introduction

section Demo1

/-- A natural number `n` is *odd*, if there exists `k : ℕ` such that `n = 2 * k + 1`. -/
def Odd (n : ℕ) : Prop :=
  ∃ (k : ℕ), n = 2 * k + 1

/-- Multiplying two odd numbers yields an odd number. -/
lemma Odd.mul {n m : ℕ} (hn : Odd n) (hm : Odd m) : Odd (n * m) := by
  /- Unfold the definition of `Odd` in the assumption `hn`. -/
  unfold Odd at hn
  unfold Odd at hm
  /- Unfold the definition of `Odd` in the goal. -/
  unfold Odd at ⊢
  /- Obtain a witness of the existential statement `∃ k, n = 2 * k + 1`. -/
  obtain ⟨k, hk⟩ := hn
  obtain ⟨l, hl⟩ := hm
  /- Rewrite in the goal with hypothesis. -/
  rw [hk, hl]
  /- Provide a witness for an existential quantifier. -/
  use k + l + 2 * k * l
  /- Show the LHS equals the RHS by standard ring axioms. -/
  ring

/-- A natural number `n` is *even*, if there exists `k : ℕ` such that `n = 2 * k`. -/
def Even (n : ℕ) : Prop :=
  ∃ (k : ℕ), n = 2 * k

/-- The sum of two odd numbers is even. -/
lemma Odd.add {n m : ℕ} (hn : Odd n) (hm : Odd m) : Even (n + m) := by
  unfold Odd at hn hm
  unfold Even at ⊢
  obtain ⟨k, hk⟩ := hn
  obtain ⟨l, hl⟩ := hm
  rw [hk, hl]
  use k + l + 1
  ring

end Demo1

section Demo2

/--
The sequence `u : ℕ → ℝ` converges to `x : ℝ` if for every `ε > 0`,
there exists `n₀ : ℕ` such that for all `n ≥ n₀`, `|x - u n| ≤ ε`.
-/
def ConvergesTo (u : ℕ → ℝ) (x : ℝ) : Prop :=
  ∀ ε > 0, ∃ (n₀ : ℕ), ∀ n ≥ n₀, |u n - x| ≤ ε

/--
A function `f : ℝ → ℝ` is continuous at `x₀` if
`∀ ε > 0, ∃ δ > 0, ∀ x, |x - x₀| ≤ δ ⇒ |f(x) - f(x₀)| ≤ ε`.
This condition will be spelled `ContinuousAt f x₀`.
-/
def ContinuousAt (f : ℝ → ℝ) (x₀ : ℝ) :=
  ∀ ε > 0, ∃ δ > 0, ∀ x, |x - x₀| ≤ δ → |f x - f x₀| ≤ ε

/--
Now we claim that if `f` is continuous at `x₀` then it is sequentially continuous
at `x₀`: for any sequence `u` converging to `x₀`, the sequence `f ∘ u` converges
to `f x₀`.

Every thing on the next line describes the objects and assumptions, each with its name.
The following line is the claim we need to prove.
-/
example (f : ℝ → ℝ) (u : ℕ → ℝ) (x₀ : ℝ) (hu : ConvergesTo u x₀) (hf : ContinuousAt f x₀) :
    ConvergesTo (f ∘ u) (f x₀) := by
  -- unfold definitions
  unfold ConvergesTo at ⊢
  unfold ContinuousAt at hf
  unfold ConvergesTo at hu
  -- fix a `ε > 0`
  intro ε hε
  -- by continuity of `f`, there exists `δ > 0` such that `∀ x, |x - x₀| ≤ δ → |f x - f x₀| ≤ ε` (1)
  obtain ⟨δ, hδ, Hf⟩ := hf ε hε
  -- by convergence of `u`, there exists `n₀ : ℕ` such that for all `n ≥ n₀`, `|u n - x₀| ≤ ε` (2)
  obtain ⟨n₀, hn₀⟩ := hu δ hδ
  -- let's prove that `n₀` works
  use n₀
  -- fix `n ≥ n₀`
  intro n hn
  -- simplify the goal
  simp
  -- by (1), it suffices to prove `|u n - x₀| ≤ δ`
  apply Hf
  -- by (2), it suffices to prove `n ≥ n₀`
  apply hn₀
  -- but we know this already!
  apply hn
  -- so we are done!

end Demo2

end Introduction
