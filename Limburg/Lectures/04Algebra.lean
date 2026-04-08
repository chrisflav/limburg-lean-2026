/-
Copyright (c) 2025 Christian Merten. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Merten
-/
import Mathlib

/-!
# Constructing new types and algebraic structures

In this lecture we cover how to construct new types and define algebraic structures.
We will cover:

- algebraic hierarchy in mathlib
- quotients
-/

noncomputable section

/-
We can define a new type by using the `structure` keyword.
-/
structure PointOnCircle where
  x : ℝ
  y : ℝ
  h : x ^ 2 + y ^ 2 = 1

/- To define a term of `PointOnCircle`, we can use the `where` keyword, ... -/
def northPole : PointOnCircle where
  x := 0
  y := 1
  h := by simp

/- ... or the `{ ... }` syntax. -/
example : PointOnCircle :=
  { x := Real.sqrt 2 / 2
    y := Real.sqrt 2 / 2
    h := by rw [div_pow]; norm_num }

/- We can inspect the fields of a structure using `#print`. -/
#print PointOnCircle

/- We can access the fields of a structure using the names of the fields, e.g.: -/
example (p : PointOnCircle) : ℝ :=
  p.x + p.y * 2

section Hierarchy

/-
Let us now look at `mathlib`s own algebraic typeclasses:
-/

#check Mul
#check Semigroup
#check Monoid
#check Group
#check CommGroup

/- and the same for additive, so e.g. -/

#check AddGroup

end Hierarchy

namespace Playground

/-
Besides the `structure` command, there is a different way to construct new types:
By taking quotients by equivalence relations.
-/

/-- A relation on integers: Two integers are equivalent if and only if their difference is
divisible by `n`. -/
def Rel (n : ℤ) (x y : ℤ) : Prop := n ∣ x - y

/-- `Rel` is an equivalence relation. -/
lemma Rel.equivalence (n : ℤ) : Equivalence (Rel n) where
  refl x := by
    sorry
  symm {x y} hxy := by
    sorry
  trans {x y z} hxy hyz := by
    sorry

/-- An equivalence relation on `ℤ`. -/
def modSetoid (n : ℤ) : Setoid ℤ where
  r := Rel n
  iseqv := Rel.equivalence n

/-- The type of integers modulo `n`: The quotient of `ℤ` by the relation `Rel`. -/
abbrev Mod (n : ℤ) : Type :=
  Quotient (modSetoid n)

/-- An addition on the integers modulo `n`. -/
instance (n : ℤ) : Add (Mod n) where
  add := by
    /- We use the universal property of the quotient: To define a function out of `Mod n`, it
    suffices to define a function out of `ℤ` that is constant on equivalence classes.
    `⟦x⟧` (type with `\[[` and `\]]`) is notation for the image of `x` in the quotient `Mod n`.
    -/
    apply Quotient.lift₂ (fun x y ↦ ⟦x + y⟧)
    sorry

lemma mk_add (n : ℤ) (x y : ℤ) : (⟦x + y⟧ : Mod n) = ⟦x⟧ + ⟦y⟧ := by
  rfl

instance (n : ℤ) : Zero (Mod n) where
  zero := sorry

lemma zero_def (n : ℤ) : (0 : Mod n) = ⟦0⟧ := by
  sorry

instance (n : ℤ) : Neg (Mod n) where
  neg := sorry

lemma mk_neg (n : ℤ) (x : ℤ) : (⟦-x⟧ : Mod n) = -⟦x⟧ := by
  sorry

instance (n : ℤ) : AddGroup (Mod n) where
  -- ignore these two
  nsmul := nsmulRec
  zsmul := zsmulRec
  zero_add x := sorry
  add_zero := sorry
  add_assoc := sorry
  neg_add_cancel := sorry

end Playground
