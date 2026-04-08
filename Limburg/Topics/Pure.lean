/-
Copyright (c) 2026 Christian Merten. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Merten
-/
import Mathlib

/-!
# Pure ideals

In this file we apply a bit of theory of pure ideals to show certain ring maps are
isomorphisms.
-/

variable {R S : Type} [CommRing R] [CommRing S] [Algebra R S]

/-- If `S` is a flat `R`-algebra such that `R →+* S` is surjective and induces
a bijection on prime spectra, then `R →+* S` is an isomorphism. -/
lemma algebraMap_bijective_of_flat_of_comap_bijective [Module.Flat R S]
    (h : Function.Surjective (algebraMap R S))
    (hbij : Function.Bijective (PrimeSpectrum.comap (algebraMap R S))) :
    Function.Bijective (algebraMap R S) :=
  -- The kernel of `R →+* S` is a pure ideal (`Ideal.Pure`). Then
  -- use `Ideal.zeroLocus_inj_of_pure` to show that the kernel is `0`.
  sorry

/-- If `S` is a faithfully flat `R`-algebra such that `R →+* S` is an epimorphism,
`R →+* S` is an isomorphism. -/
lemma algebraMap_bijective_of_isEpi [Algebra.IsEpi R S] [Module.FaithfullyFlat R S] :
    Function.Bijective (algebraMap R S) :=
  -- Use `Module.FaithfullyFlat.bijective_of_tensorProduct`
  sorry
