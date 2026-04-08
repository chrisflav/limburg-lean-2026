/-
Copyright (c) 2025 Christian Merten. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Merten
-/
import Mathlib

/-!
# Topic: Zariski topology on the prime spectrum

In this file we define the Zariski topology on the prime spectrum of a ring.
-/

/-
In order to say “Let `R` a an arbitrary commutative ring, we write
`{R : Type} [CommRing R]` to declare a type `R` and then assume it is equipped
with a commutative ring structure.
-/
variable {R : Type} [CommRing R]

/-
The type of ideals of `R` is `Ideal R`. The ideals form a lattice, i.e. we can
take infima and suprema of ideals:
-/
variable (I J K : Ideal R)
#check I ⊓ (J ⊔ K)

/- The predicate of an ideal being prime is called `Ideal.IsPrime`. -/
#check Ideal.IsPrime

/-- A term of `Spec R` is a prime ideal of `R`. -/
structure Spec (R : Type) [CommRing R] where
  ideal : Ideal R
  isPrime : ideal.IsPrime

attribute [instance] Spec.isPrime

/-- The zero locus of a set of elements in `R` is the set of primes containing `s`. -/
def zeroLocus (s : Set R) : Set (Spec R) :=
  { p | s ⊆ p.ideal }

lemma mem_zeroLocus (s : Set R) (p : Spec R) :
    p ∈ zeroLocus s ↔ s ⊆ p.ideal := .rfl

/-- The zero locus is inclusion reversing. -/
lemma zeroLocus_subset_of_subset {s t : Set R} (hst : s ⊆ t) :
    zeroLocus t ⊆ zeroLocus s :=
  sorry

lemma zeroLocus_span (s : Set R) : zeroLocus (Ideal.span s) = zeroLocus s :=
  sorry

lemma zeroLocus_radical (I : Ideal R) :
    zeroLocus (I.radical : Set R) = zeroLocus I :=
  sorry

lemma zeroLocus_union (s t : Set R) :
    zeroLocus (s ∪ t) = zeroLocus s ∩ zeroLocus t := by
  sorry

lemma zeroLocus_iUnion {ι : Type} (s : ι → Set R) :
    zeroLocus (⋃ i, s i) = ⋂ i, zeroLocus (s i) := by
  sorry

lemma zeroLocus_inf (I J : Ideal R) :
    zeroLocus (I ⊓ J : Set R) = zeroLocus I ∪ zeroLocus J := by
  sorry

lemma union_zeroLocus (s t : Set R) :
    zeroLocus s ∪ zeroLocus t = zeroLocus (Ideal.span s ⊓ Ideal.span t) := by
  sorry

/--
The prime spectrum of `R` carries the structure of a topological space by declaring
the zero loci of ideals to be the closed sets.
-/
instance : TopologicalSpace (Spec R) := by
  refine .ofClosed { s | ∃ (I : Ideal R), s = zeroLocus I } ?_ ?_ ?_
  · sorry
  · sorry
  · sorry

/-- The basic open `D(r)` is the set of primes not containing `r`. -/
def basicOpen (r : R) : Set (Spec R) :=
  { p | r ∉ p.ideal }

/-- The basic opens are indeed open. -/
lemma isOpen_basicOpen (r : R) : IsOpen (basicOpen r) :=
  sorry

/--
Challenge: The prime spectrum of a ring is quasi-compact.
Hint: Observe first that the basic opens of `Spec R` form a basis of the topology.
-/
instance : CompactSpace (Spec R) :=
  sorry
