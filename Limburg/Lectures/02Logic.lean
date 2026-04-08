/-
Copyright (c) 2025 Raphael Douglas Giles. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Raphael Douglas Giles, Christian Merten
-/
import Mathlib

/-!

# Lecture: Logic and Sets

In this first lecture, we're going to explore how to prove basic statements
in propositional and predicate logic in lean, and we're also going to see
how to work with sets and functions.

-/

section

/-!
# Propositions as types

As seen in the introduction, propositions are a special case of types and
giving a proof of a proposition `p` is the same as giving a term `hp : p`.

`p : Prop` means that `p` is a type with either zero or one inhabitants. The
inhabitants should be interpreted as proofs of the proposition encoded by `p`.
-/

/-
This encodes the following fact:

Given an arbitrary proposition `p`, `p` implies `p`.
-/
example (p : Prop) : Prop := p → p

/-
Note that a proposition does not need to be true to be well typed! It just means that we
cannot construct an inhabitant of this type (i.e. a proof of this proposition).
-/
example : Prop := ∀ n : ℕ, 2 * n = n

example (s : ℕ → ℝ) (L : ℝ) : Prop :=
  ∀ ε > 0, ∃ N : ℕ, ∀ n ≥ N, |s n - L| ≤ ε

/-!
## Logical connectives, some examples

The way we prove a statement in logic depends a little bit on the *logical
connectives* involved, so we'll organise our discussion around that. First,
let's discuss *implication*.
-/


/-! ### Implications
An implication `p → q` is encoded by a function from `p` to `q`, the idea being that
one can view such an implication as a machine which turns a proof of `p` into a proof
of `q`.

To write the symbol `→`, use `\to`.

Relevant tactics:

When in goal: `intro`
When in hypothesis: `have` or `apply`
-/

example (p : Prop) : p → p := by
  sorry

example (p q : Prop) : p → (q → p) := by
  sorry

example (p q r : Prop) : (p → q) → ((p → (q → r)) → (p → r)) := by
  sorry

/-! ### Universal quantification

Forall statements are also encoded by functions, but where the
codomain may depend on the bound variable.
Practially speaking, this means that dealing with foralls is
very similar to dealing with implications.

To write the `∀` symbol, use `\forall`

The same tactics used in implications are relevant here.
-/

/-
This is just another way of writing our first example
-/
example : ∀ p : Prop, p → p := by
  sorry

example (α : Type) (p q : α → Prop) (h : ∀ x, p x → q x) :
    (∀ x, p x) → ∀ x', q x' := by
  sorry

/-! ### Existential quantifier
A proof of an existential statemtent `∃ x, p x`
is a pair of a *witness* `x` and a proof that `p x` holds.

To write the `∃` symbol, use `\exists`

Relevant tactics:

When in goal: `use`
When in hypothesis: `obtain`
-/

example : ∃ n : ℕ, n < n + 1 := by
  sorry

example : ∃ n : ℕ, n = n :=
  sorry

example (f : ℕ → ℕ) (hf : ∀ m, ∃ n, m ≤ f n) :
    ∀ m, ∃ n, m ≤ 2 * f n := by
  sorry

/-! ### Conjunctions

To prove a conjunction `a ∧ b`, we need to provide a proof of `a` and a proof of `b`.

To write the `∧` symbol, use `\and`

Relevant tactics:

When in goal: `constructor`
When in hypothesis: `obtain`

If `h : p ∧ q` then `h.1 : p` and `h.2 : q`.
We can also say `h.left` or `h.right`
-/

example (p q : Prop) : p → q → p ∧ q := by
  sorry

example (p q : Prop) : p ∧ q → q ∧ p := by
  sorry

/-! ### Disjunctions
To prove a disjunction `a ∨ b`, we need to either prove `a` or `b`.

To write the `∨` sumbol, use `\or`

Relevant tactics:

When in goal: `left`, `right
When in hypothesis: `obtain`
-/

example (p q : Prop) : p → p ∨ q := by
  sorry

example (p q : Prop) : p ∨ q → q ∨ p := by
  sorry

/-! ### Iffs

To prove an iff statement `p ↔ q`, we need to prove `p → q` and `q → p`.

To write the `↔` symbol, use `\iff`

Relevant tactics:

When in goal: `constructor`

When in hypothesis: `rw`, etc. since we
can rewrite with `↔` statements.

If `h : p ↔ q` then `h.mp : p → q` and `h.mpr : q → p`
-/

example (p q : Prop) : (p ↔ q) ↔ (p → q) ∧ (q → p) := by
  sorry

/-! ### Negation
`¬ p` is actually *defined* in lean to be `p → False`. So we can just work with
it like any other implication.

To write the `¬` symbol, use `\not`

Relevant tactics:

When in goal: `intro`
When in hypothesis: `apply` (if goal is `False`), `have`

-/

/-
Here is an example showing `¬ p` and `p → False` really give the same thing.
-/
example (p : Prop) : ¬ p ↔ (p → False) := Iff.rfl

example (p q : Prop) (h : p → q) : ¬ q → ¬ p := by
  sorry

/-
From `False` we can derive anything, and we have a few different methods for showing this.
-/
example (p q : Prop) (hp : p) (hpq : ¬ p) : q := by
  sorry

end

namespace MySets

/-- A (sub)set of `α` is a predicate on `α`. -/
def Set (α : Type) : Type := α → Prop

variable (α β : Type)

/-- Enable `∈` notation. -/
instance : Membership α (Set α) where
  mem s := s

/-- Two sets are equal if and only if they contain the same elements. -/
lemma Set.ext (s t : Set α) : s = t ↔ ∀ x, x ∈ s ↔ x ∈ t := by
  sorry

/-- The universal set of `α: The set containing all terms of `α`. -/
def Set.univ : Set α := sorry

/-- The empty set of `α: The set containing nothing. -/
def Set.empty : Set α := sorry

/-- The preimage of `s` under `f` is `{ x : α | f x ∈ s }`. -/
def Set.preimage (f : α → β) (s : Set β) : Set α :=
  fun x ↦ f x ∈ s

/-- The image of `s` under `f` is `{ f x | x ∈ s }`. -/
def Set.image (f : α → β) (s : Set α) : Set β :=
  fun y ↦ ∃ x ∈ s, f x = y

end MySets

variable (α β : Type)

example (f : α → β) (s t : Set β) : f ⁻¹' (s ∩ t) = f ⁻¹' s ∩ f ⁻¹' t := by
  apply Set.ext
  intro x
  constructor
  · intro hx
    rw [Set.mem_preimage, Set.mem_inter_iff] at hx
    rw [Set.mem_inter_iff, Set.mem_preimage]
    exact hx
  · sorry

namespace MyDefs

/--
In Mathlib, a set of elements of `α` is a predicate with domain `α`,
i.e. a function `p : α → Prop`. The idea is that for some `x : α`,
`p a` should be true if `a` is in the set and false otherwise.

We denote the type of all such functions by `Set α`.
If we regard `α` as iteslf being a set, then the type `Set α`
is the power set of `α`. -/

def Set (α : Type*) := (α → Prop)

variable {α : Type*}

/--
Interpret a predicate `p : α → Prop` as a set.
-/
def setOf (p : α → Prop) : Set α := p

/-- Enable `∈` notation. -/
instance : Membership α (Set α) where
  mem s x := s x

/-
This says that Set.mem is really just the proposition that the set is
defined to be
-/
lemma Set.mem_iff (x : α) (s : Set α) : x ∈ s ↔ s x := Iff.rfl

/-
When defining new data structures, we often write "extensionality"
lemmas (usually denoted with `_.ext`). These say that "two things are the same
if they contain the same stuff".

For example, we have `funext`, which says that two functions `f g : α → β`
are equal if `f x = g x` for all `x : α`.

We also have `propext`, which says that two propositions `a` and `b` are
equal if `a ↔ b`.

We're going to show an extensionality lemma for sets `Set.ext`,
which says that two sets are equal iff they have the same elements.
-/
#check funext
#check propext

lemma Set.ext (s t : Set α) : s = t ↔ ∀ x, x ∈ s ↔ x ∈ t := by
  sorry

/-
We can make our own notation using the *notation* keyword. Here,
we're making a notation which resembles the familiar set builder notation.

Note that lean already has a built in set builder notation, so we've added
this funny `my` at the start so that lean doesn't complain.
-/
notation "my{" x " | " p "}" => setOf fun x => p

#check my{(n : Nat) | 0 < n}

/-
Write the following common set operations using our set builder notation:
-/

/-- s ∪ t -/
def Set.union (s t : Set α) : Set α :=
  sorry

/-- s ∩ t -/
def Set.inter (s t : Set α) : Set α :=
  sorry

/-- s \ t -/
def Set.diff (s t : Set α) : Set α :=
  sorry

/-- sᶜ -/
def Set.compl (s : Set α) : Set α :=
  sorry

/-- s ⊆ t -/
def Set.IsSubset (s t : Set α) : Prop := ∀ x, x ∈ s → x ∈ t

/-- ∅ -/
def Set.empty : Set α :=
  sorry

/-- Set.univ : Set α should be α regarded as a set -/
def Set.univ : Set α :=
  sorry

lemma Set.mem_union (s t : Set α) (x : α) : x ∈ Set.union s t ↔ x ∈ s ∨ x ∈ t := by
  sorry

lemma Set.mem_inter_iff (s t : Set α) (x : α) : x ∈ Set.inter s t ↔ x ∈ s ∧ x ∈ t :=
  sorry

end MyDefs

#check Set.mem_diff
#check Set.mem_compl_iff
#check Set.subset_def

open Set

/-
From this point on we have exited the `MyDefs` namespace and are just
working with the existing `Set` library in lean. This is just so we have
access to more lemmas so we can prove more interesting statements, the
lean library under the hood looks more or less like what we've developed
above.
-/


variable {α β : Type*} (s t u : Set α)

/-
The following is a fairly simple set theory lemma, and we're going to prove
it in a few different ways
-/

example (h : s ⊆ t) : s ∩ u ⊆ t ∩ u := by
  sorry

example (h : s ⊆ t) : s ∩ u ⊆ t ∩ u := by
  sorry

/-
To prove set theoretic statements using logic, it often helps to turn them
into statements about *membership*, for which our `ext` lemma we proved before
can be helpful.

The `ext` tactics applies relevant `ext` lemmas in the given context. We can then
prove this statement using only `mem_union` and `Or.comm`.
-/
example : s ∪ t = t ∪ s := sorry


/-! ## Functions -/

/-
So far we have seen the `→` symbol used for implications, but it can also
be used to denote functions! In fact, this is more than just a notational
trick, as we have seen under the hood these are really the same thing.
-/
variable (f : α → β)

/-
Here we can define function composition, and notice how it's exactly
the same as proving the transitivity of implication.
-/
example {γ : Type*} (g : α → β) (h : β → γ) : α → γ := sorry

#check Set.preimage
example (s : Set β) : f ⁻¹' s = {x | f x ∈ s} := rfl

#check Set.image
example (s : Set α) : f '' s = {y | ∃ x, x ∈ s ∧ f x = y} := rfl


/-
The following lemmas are quite useful when working with images and
preimages
-/
#check Set.mem_preimage

#check Set.mem_image

/-
Here is a simple statement about preimages of sets. To give a sense of how
much more powerful lean's `rfl` tactic is than its counterpart in the natural
numbers game, we note that this lemma can actually be proven by `rfl`.

To make this slightly more interesting, let's try and prove this just using the
following limited set of lemmas:

`union_def`
`setOf_or`
`mem_setOf`
`mem_union`
`Set.mem_preimage`

We're also allowed to use tactics like `rw`, `apply`, `unfold`, `ext` and so on
(but no simp!)
-/
example (u v : Set β) : f ⁻¹' (u ∪ v) = f ⁻¹' u ∪ f ⁻¹' v := by
  sorry
