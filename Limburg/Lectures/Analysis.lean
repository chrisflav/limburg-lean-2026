/-
Copyright (c) 2025 Christian Merten. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Merten
-/
import Mathlib

/-!
# Lecture: Real analysis and linear arithmetic in Lean

In this lecture we cover the basic interactions with the real numbers in Lean.
We will cover

- real (in)equalities
- example: convergence of sequences
- natural numbers, casting and junk values

## References

Some of the examples are taken from:

- Jeremy Avigad, Patrick Massot: Mathematics in Lean
  (https://leanprover-community.github.io/mathematics_in_lean)
- Kevin Buzzard: Formalising Mathematics
  (https://github.com/ImperialCollegeLondon/formalising-mathematics-2024)
-/

section Reals

/-
The real numbers in Lean are actual real numbers, not floating point
approximations.
Internally, they are implemented via Cauchy sequences of rational numbers.
-/
#check ℝ

/- The real number `2` is represented by the constant Cauchy sequence `2, 2, 2, ...`. -/
#eval (2 : ℝ)

/- This is the statement that `2 + 2 = 4` as an equality in the natural numbers. -/
example : 2 + 2 = 4 :=
  rfl

/- This is the statement that `2 + 2 = 4` as an equality in the real numbers. -/
example : (2 : ℝ) + 2 = 4 := by
  sorry

/- Identities with real variables can be proven using `rw` with lemmas from the library. -/
example (x y : ℝ) : (x + y) ^ 2 = x ^ 2 + 2 * x * y + y ^ 2 := by
  rw [sq, sq, sq]
  rw [mul_add, add_mul, add_mul]
  rw [mul_comm y x, ← add_assoc, add_assoc (x * x)]
  rw [two_mul, add_mul]

/- This becomes quite tedious, so there exists the `ring` tactic that proves any
identity that holds in any commutative ring. -/
example (x y : ℝ) : (x + y) ^ 2 = x ^ 2 + 2 * x * y + y ^ 2 := by
  sorry

example : ∀ a b : ℝ, ∃ x, (a + b) ^ 3 = a ^ 3 + x * a ^ 2 * b + 3 * a * b ^ 2 + b ^ 3 := by
  sorry

/- `mathlib` defines many standard functions on the real numbers, such as `sin` and `cos`. -/
/--
info: Real.sin : ℝ → ℝ
-/
#guard_msgs in
#check (Real.sin : ℝ → ℝ)

example (x : ℝ) : Real.sin x ^ 2 + Real.cos x ^ 2 = 1 := by
  sorry

end Reals

section Inequalities

/- The real numbers are ordered and we can use many lemmas from the library to close simple
goals. -/
example (x : ℝ) : x ≤ x := by
  apply le_refl

example {x y z : ℝ} (hxy : x ≤ y) (hyz : y ≤ z) : x ≤ z := by
  apply le_trans
  · apply hxy
  · apply hyz

/-
We can find lemma names by using the library search tactic `exact?`.
-/
/--
info: Try this:
  [apply] exact abs_add_le x y
-/
#guard_msgs in
example (x y : ℝ) : |x + y| ≤ |x| + |y| := by
  exact?

/- We can also use the trans tactic. -/
example {x y z : ℝ} (hxy : x ≤ y) (hyz : y ≤ z) : x ≤ z := by
  trans y
  · apply hxy
  · apply hyz

/- Or the calc tactic. -/
example {x y z : ℝ} (hxy : x ≤ y) (hyz : y = z) : x ≤ z := by
  calc
    x ≤ y := by apply hxy
    _ = z := by apply hyz

/- Or use `linarith` to close linear arithmetic goals. -/
example {x y z : ℝ} (hxy : x ≤ y) (hyz : y = z) : x ≤ z := by
  linarith

/- A slightly more complicated example. -/
example {a b : ℝ} : 2 * a * b ≤ a ^ 2 + b ^ 2 := by
  have h : 0 ≤ a ^ 2 - 2 * a * b + b ^ 2 := by
    calc
      a ^ 2 - 2 * a * b + b ^ 2 = (a - b) ^ 2 := by ring
                              _ ≥ 0 := by positivity
  calc
    2 * a * b = 2 * a * b + 0 := by ring
            _ ≤ 2 * a * b + (a ^ 2 - 2 * a * b + b ^ 2) := by linarith
            _ = a ^ 2 + b ^ 2 := by ring

end Inequalities

section CaseSplitting

example (x y : ℝ) : x < |y| → x < y ∨ x < -y := by
  -- a new usage of the `obtain` tactic: We case split on an `or` statement.
  obtain h | h := le_or_gt 0 y
  -- step through this proof to observe.
  · rw [abs_of_nonneg h]
    intro h
    -- We want to show an `∨` statement, by showing the left case is true.
    left
    exact h
  · rw [abs_of_neg h]
    intro h
    -- We want to show an `∨` statement, by showing the right case is true.
    right
    exact h

end CaseSplitting

section Sequences

/- A sequence of real numbers is a function `ℕ → ℝ`. -/
variable (a : ℕ → ℝ)

/- The `5`-th entry of the sequence `a` is simply `a 5`. -/
#check a 5

/--
The sequence `a : ℕ → ℝ` converges to `x : ℝ` if for every `ε > 0`,
there exists `n₀ : ℕ` such that for all `n ≥ n₀`, `|x - a n| ≤ ε`.
-/
def ConvergesTo (a : ℕ → ℝ) (x : ℝ) : Prop :=
  ∀ ε > 0, ∃ (n₀ : ℕ), ∀ n ≥ n₀, |x - a n| ≤ ε

/- Use `rw [convergesTo_iff]` to unfold the definition of convergence. -/
lemma convergesTo_iff (a : ℕ → ℝ) (x : ℝ) :
    ConvergesTo a x ↔ ∀ ε > 0, ∃ (n₀ : ℕ), ∀ n ≥ n₀, |x - a n| ≤ ε := by
  rfl

/-- Any constant sequence converges to its value. -/
lemma ConvergesTo.const (a : ℝ) : ConvergesTo (fun _ ↦ a) a := by
  sorry

/-- If `a` converges to `x` and `b` converges to `y`, then
`a + b` converges to `x + y`. -/
lemma ConvergesTo.add {a b : ℕ → ℝ} {x y : ℝ}
    (ha : ConvergesTo a x) (hb : ConvergesTo b y) :
    ConvergesTo (a + b) (x + y) := by
  sorry

/--
The sequence `a : ℕ → ℝ` is bounded if there exists a constant `M : ℝ` such that
`|a n| ≤ M` for all `M`.
-/
def Bounded (a : ℕ → ℝ) : Prop :=
  ∃ (M : ℝ), ∀ n, |a n| ≤ M

lemma bounded_iff (a : ℕ → ℝ) :
    Bounded a ↔ ∃ (M : ℝ), ∀ n, |a n| ≤ M := by
  rfl

/--
If `a : ℕ → ℝ` is bounded by `M` for almost all `n : ℕ`, it is bounded
everywhere.
-/
lemma Bounded.of_le {a : ℕ → ℝ} (M : ℝ) (n₀ : ℕ) (h : ∀ n ≥ n₀, |a n| ≤ M) :
    Bounded a := by
  rw [bounded_iff]
  let s : Finset ℕ := Finset.range (n₀ + 1)
  use M + s.sup' ⟨0, by simp [s]⟩ (fun k ↦ |a k|)
  intro m
  by_cases hm : n₀ ≤ m
  · trans
    · exact h m hm
    · simp only [le_add_iff_nonneg_right, Finset.le_sup'_iff]
      use 0
      simp [s]
  · have hmem : m ∈ s := by simp [s]; omega
    trans
    · exact Finset.le_sup' (fun k ↦ |a k|) hmem
    · have : 0 ≤ M := (abs_nonneg (a n₀)).trans (h n₀ (Nat.le_refl n₀))
      simpa

/-- Any convergent sequence is bounded. -/
lemma ConvergesTo.bounded {a : ℕ → ℝ} {x : ℝ} (h : ConvergesTo a x) :
    Bounded a := by
  obtain ⟨n₀, hn₀⟩ := h 1 (by linarith)
  apply Bounded.of_le (|x| + 1) n₀
  intro n hn
  specialize hn₀ n hn
  calc
    |a n| = |(a n - x) + x| := by sorry
        _ ≤ |a n - x| + |x| := by sorry
        _ = |x - a n| + |x| := by sorry
        _ ≤ 1 + |x| := by sorry
        _ = |x| + 1 := by sorry

/-- If `a` converges to `x` and `b` converges to `y`, then `a * b` converges
to `x * y`. -/
lemma ConvergesTo.mul {a b : ℕ → ℝ} {x y : ℝ} (ha : ConvergesTo a x)
    (hb : ConvergesTo b y) :
    ConvergesTo (a * b) (x * y) := by
  intro ε hε
  obtain ⟨M, hM⟩ := ha.bounded
  let C : ℝ := |M| + |y| + 1
  have : 0 < C := by
    simp only [C]
    positivity
  obtain ⟨n₀, hn₀⟩ := ha (ε / (2 * C)) (by positivity)
  obtain ⟨m₀, hm₀⟩ := hb (ε / (2 * C)) (by positivity)
  use max n₀ m₀
  intro n hn
  have : 0 ≤ |M| := by positivity
  have : 0 ≤ |y| := by positivity
  have : |y| ≤ C := by
    simp only [C]
    sorry
  have : |a n| ≤ C := by
    sorry
  calc
    |x * y - (a * b) n| = |x * y - a n * b n| := by sorry
                      _ = |(x - a n) * y + a n * (y - b n)| := by sorry
                      _ ≤ |(x - a n) * y| + |a n * (y - b n)| := by sorry
                      _ = |x - a n| * |y| + |a n| * |y - b n| := by sorry
                      _ ≤ ε / (2 * C) * C + C * (ε / (2 * C)) := ?_
                      _ = ε := by field_simp; ring
  gcongr ?_ * ?_ + ?_ * ?_
  · sorry
  · sorry

end Sequences
