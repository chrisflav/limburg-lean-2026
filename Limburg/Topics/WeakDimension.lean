/-
Copyright (c) 2026 Christian Merten. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Merten
-/
import Mathlib

/-!
# Weak dimension of rings

In this file we develop the basic notion of rings of weak dimension `≤ 1`. These
are rings for which every ideal is flat.
-/

/-- A ring `R` is of weak dimension `≤ 1` if every ideal is flat. -/
class WeakDimensionLEOne (R : Type) [CommRing R] : Prop where
  flat (I : Ideal R) : Module.Flat R I

variable {k R : Type} [CommRing R]

/- Pre-warm-up: Any field is of weak dimension `≤ 1`. -/
example [Field k] : WeakDimensionLEOne k := by
  -- Hint: Use the `infer_instance` tactic, which tries to search for certain
  -- conclusions in the library.
  sorry

/-- Warm-up: Any valuation ring is of weak dimension `≤ 1`. -/
instance [IsDomain R] [ValuationRing R] : WeakDimensionLEOne R :=
  sorry

-- Don't work on this unless you really want a challenge :)
/-- If `R` is of weak dimension `≤ 1`, any submodule of a flat module is flat. -/
@[stacks 092S]
instance (priority := low) Submodule.flat [WeakDimensionLEOne R] {M : Type} [AddCommGroup M]
    [Module R M] (N : Submodule R M) [Module.Flat R M] :
    Module.Flat R N :=
  sorry

/-- Let `Aᵢ` be a family of `R`-algebras and `Mᵢ` is a family
of `Aᵢ`-modules. If `N` is an `∏ᵢ, Aᵢ`-submodule of `∏ᵢ, Mᵢ` and
`Nᵢ` is the image of `N` in `Mᵢ`, then `N ≤ ∏ᵢ, Nᵢ`.
Equality holds if `N` is finitely generated (see below). -/
lemma Submodule.le_pi (ι : Type) (A : ι → Type) (M : ι → Type)
    [∀ i, CommRing (A i)] [∀ i, Algebra R (A i)]
    [∀ i, AddCommGroup (M i)] [∀ i, Module (A i) (M i)]
    [∀ i, Module R (M i)] [∀ i, IsScalarTower R (A i) (M i)]
    (N : Submodule (Π i, A i) (Π i, M i)) :
    N.restrictScalars R ≤
      Submodule.pi .univ fun i ↦ (N.restrictScalars R).map (LinearMap.proj _) :=
  sorry

/-- Equality case of `Submodule.le_pi`. -/
lemma Submodule.pi_eq_of_fg (ι : Type) (A : ι → Type) (M : ι → Type)
    [∀ i, CommRing (A i)] [∀ i, Algebra R (A i)]
    [∀ i, AddCommGroup (M i)] [∀ i, Module (A i) (M i)]
    [∀ i, Module R (M i)] [∀ i, IsScalarTower R (A i) (M i)]
    (N : Submodule (Π i, A i) (Π i, M i)) (hN : N.FG) :
    N.restrictScalars R =
      Submodule.pi .univ fun i ↦ (N.restrictScalars R).map (LinearMap.proj _) :=
  sorry

/-- A product of valuation rings is of weak dimension `≤ 1`. -/
@[stacks 092T]
instance (ι : Type) (A : ι → Type) [∀ i, CommRing (A i)]
    [∀ i, IsDomain (A i)] [∀ i, ValuationRing (A i)] :
    WeakDimensionLEOne (Π i, A i) :=
  -- Uses `Submodule.pi_eq_of_fg`.
  sorry

/-- If `R` is of weak dimension `≤ 1` and `R →+* A` is a flat, injective epimorphism of rings,
then `R` is integrally closed in `A`. -/
@[stacks 092V]
lemma isIntegrallyClosedIn_of_weakDimensionLEOne [WeakDimensionLEOne R] {A : Type}
    [CommRing A] [Algebra R A] [Module.Flat R A] (h : Function.Injective (algebraMap R A))
    [Algebra.IsEpi R A] :
    IsIntegrallyClosedIn R A :=
  -- uses `Submodule.flat`
  -- Hint: `Algebra.isEpi_iff_surjective_algebraMap_of_finite`
  sorry
