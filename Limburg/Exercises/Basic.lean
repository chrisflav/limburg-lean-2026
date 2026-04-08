/-
Copyright (c) 2026 Christian Merten. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Merten
-/
import Mathlib

/-!

# Basics

This file teaches you the basics of Lean in many examples. The file contains many `sorry`s. These
are placeholders that you should try to fill with proofs.

## References

The examples in this file are taken from Patrick Massot's
[Glimpse of Lean](https://github.com/PatrickMassot/GlimpseOfLean/blob/master/GlimpseOfLean/Exercises/01Rewriting.lean).
-/

namespace Playground

/-!
## Rewriting and computing

The first thing we learn is how to "compute". Of course, by computing we don't mean computing, but
performing symbolical manipulations to show certain equalities.
-/

open Real

/-
Computations that only rely on the properties of a commutative ring, can be handled
by the `ring` tactic.
-/
example (x y z : ℤ) : x + y * z = z * y + x := by
  ring

example (x y : ℤ) : (x + y) ^ 2 = 2 * x * y + y ^ 2 + x * x := by
  sorry

/-
`ring` does not use local hypothesis. To use them, we can *rewrite* with that equality instead.
Rewriting with an equality `x = y` means replacing every occurence of `x` in the goal
with `y`.
-/
example (a b c d e : ℤ) (h : a = b + c) (h' : b = d - e) : a + e = d + c := by
  rw [h]
  sorry

example (a b c d e : ℝ) (h : a = b + c) (h' : a + e = d + c) : b + c + e = d + c := by
  /-
  To rewrite with the RHS of an equality, we can rewrite from right to left using `←`.
  (this can be typed as `\` + `l`)
  -/
  rw [← h]
  sorry

example (a b c d : ℤ) (h : b = d + d) (h' : a = b + c) : a + b = c + 4 * d := by
  sorry

/-
Note that some more powerful automation can close this complete goal: Try `grind`.
This uses some Gröbner basis algorithm.
-/
example (a b c d e : ℤ) (h : a = b + c) (h' : b = d - e) : a + e = d + c := by
  sorry

example (a b c : ℝ) : exp (a + b + c) = exp a * exp b * exp c := by
  -- We can also `rw` with lemmas from the library.
  rw [exp_add (a + b) c]
  sorry

/-
Sometimes we don't want to rewrite in the goal, but in some assumption. For
this we can use the `rw [..] at h` syntax.
Note: `rw [..]` is short for `rw [..] at ⊢`.
-/
example (a b c d : ℝ) (h : c = d * a + b) (h' : b = d) : c = d * a + d := by
  rw [h'] at h
  -- Our assumption `h` is now exactly what we have to prove
  apply h

/-
Longer computations can be split into `calc` blocks.
-/
example (a b c d : ℝ) (h : c = b * a - d) (h' : d = a * b) : c = 0 := by
  calc
    c = b*a - d   := by sorry
    _ = b*a - a*b := by sorry
    _ = 0         := by sorry

/-
Complete the following proof by doing a `calc` computation.
-/
example (a b c : ℝ) (h : a = b + c) : exp (2 * a) = (exp b) ^ 2 * (exp c) ^ 2 := by
  sorry

/-
You have completed the first set of exercises! Now proceed to the next stage.
-/

/-!
## Logic and the glue

Of course, mathematical proofs don't only consist of computations. We also need
to manipulate logical formulas, quantifiers etc. This section teaches you how to work with them.
-/

/-
Implications are modelled by functions `p → q` between propositions. The mental picture is:
An implication `p → q` is the guarantee that if `p` holds, then also `q` holds. In other words,
if `hp : p` is a proof of `p`, an implication `p → q` will provide a proof of `q`.

This happens by applying the function `p → q` to the term `hp : p`. The corresponding
tactic is therefore called `apply`:
-/
example (p q : Prop) (h : p → q) (hp : p) : q := by
  -- Read this as: apply `h` to `hp`
  apply h hp

example (p q : Prop) (h : p → q) (hp : p) : q := by
  -- `apply` is smarter: We don't have to provide `hp` directly:
  apply h
  /-
  What happened? `apply h` checks if the goal matches the conclusion of `h`
  (here they are both `q`).
  If they match, `apply` generates a new goal for every assumption of `h` (here only `p`).
  -/
  apply hp

example (p q r : Prop) (hpq : p → q) (hqr : q → r) (hp : p) : r := by
  sorry

/-
Observe that `p → q → r = p → (q → r)`. It is fine to think of this as a function
with two arguments, or an implication with two assumptions. But for Lean,
this is simply a function whose codomain is itself a function.
-/
example (p q r : Prop) (hpq : p → q → r) (hqr : p → q) (hp : p) : r := by
  sorry

/-
`∀`-quantifiers are similar to functions: In fact, they are dependent functions.
For example here one can also write the type of `h` as `(n : ℕ) → p n`.

`apply` works in the same way for `∀`-quantifiers as for functions.
-/
example (p : ℕ → Prop) (h : ∀ n : ℕ, p n) : p 42 := by
  sorry

/- `¬ p` is by definition `p → False`, so you are well equipped to solve the following exercise: -/
example (p : Prop) (hp : p) : ¬ ¬ p := by
  sorry

/-- A function `ℝ → ℝ` is even if for all real numbers `x : ℝ`, `f (-x) = f x` holds. -/
/-
Note: What in informal maths is usually denoted by `f(x)`, we simply write as `f x`.
-/
def Even (f : ℝ → ℝ) : Prop :=
  ∀ x : ℝ, f (-x) = f x

example (f g : ℝ → ℝ) (hf : Even f) (hg : Even g) : Even (f + g) := by
  -- Unfold the definition of `Even`
  unfold Even at hf hg ⊢
  /- New tactic: To show a `∀` or `→` statement, use the `intro` tactic to introduce
  a fresh variable. You can give the variable any name. -/
  intro x
  sorry

example (f g : ℝ → ℝ) (hf : Even f) : Even (g ∘ f) := by
  sorry

/-
Summary for `∀`, `→`:
- `apply` for `∀`, `→` in a hypothesis
- `intro` for `∀, `→` in the goal
-/

/-
We also need to manipulate existentials.
-/
example (a b c : ℤ) (h₁ : a ∣ b) (h₂ : b ∣ c) : a ∣ c := by
  -- To obtain a witness from an `∃ x, ...` hypothesis.
  obtain ⟨k, hk⟩ := h₁
  obtain ⟨l, hl⟩ := h₂
  -- To provide a witness for a `∃ x, ...` goal.
  use k * l
  sorry

example (a b c : ℤ) (h₁ : a ∣ b) (h₂ : a ∣ c) : a ∣ b + c := by
  sorry

/-
Summary for `∃`:
- `obtain` for `∃` in a hypothesis
- `use` for `∃` in the goal
-/

/-
The last connective we treat here is `∧`:
-/
example {p q : Prop} (hp : p) (hq : q) : p ∧ q := by
  -- To show an `∧`-statement, use the `constructor` tactic. It yields one goal per side.
  constructor
  · apply hp
  · apply hq

/-- if-and-only-if statements are similar to `∧` and you can also use `constructor` to show them. -/
example {p q : Prop} : p ∧ q ↔ q ∧ p := by
  -- Hint: To unfold an `∧` statement, you can use `obtain ⟨hp, hq⟩ := h` or `h.left` and `h.right`.
  sorry

/-
Congratulations! You have made it through the basics. For a summary of all of these
basic tactics, you can have a look at Patrick Massot's tactic cheatsheet:

https://github.com/PatrickMassot/GlimpseOfLean/blob/master/tactics.pdf

After that, proceed with the exercise file `Limburg/Exercises/Nilpotent.lean`.
-/

end Playground
