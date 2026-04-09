import Mathlib

/-!
# Some algebraic geometry exercise

We show how one can prove that being integral is stable under base change.
-/

universe u

open AlgebraicGeometry CategoryTheory Limits MorphismProperty TensorProduct

variable (X : Scheme.{u}) (Y : Scheme.{u}) (f : X ⟶ Y)

-- Integral morphism of schemes
#check IsIntegralHom

/-
Mathlib likes formal morphism properties, so we can also express everything in terms
of abstract properties of morphism properties.

`IsStableUnderBaseChange` says what you think it says:
-/
#check IsStableUnderBaseChange

/-- Being an integral morphism of schemes is stable under base change. -/
lemma foo : IsStableUnderBaseChange @IsIntegralHom.{u} := by
  -- Because being integral is stable under isomorphisms, it suffices
  -- to check it for some choice of fibre product.
  apply IsStableUnderBaseChange.mk'
  intro X Y S f g h hg
  /-
  We may assume that `S = Spec R` for some commutative ring `R`.
  Note that for Lean there is a difference between `S` is affine and `S` is
  *equal* to the spectrum of a ring. If possible, it is always easier if
  we can assume equality.
  -/
  wlog hS : ∃ (R : CommRingCat.{u}), S = Spec R
  · let 𝒰 : S.OpenCover := S.affineCover
    let 𝒱 : X.OpenCover := 𝒰.pullback₁ f
    -- Integral is (Zariski) local at the target
    rw [IsZariskiLocalAtTarget.iff_of_openCover (P := @IsIntegralHom) 𝒱]
    intro i
    simp [Scheme.Cover.pullbackHom]
    /-
    We manually compute an isomorphism of fibre products.
    This is the isomorphism `(X ×[S] Uᵢ) ×[X] (X ×[S] Y) ≅ (X ×[S] Uᵢ) ×[Uᵢ] (Y ×[S] Uᵢ)`.
    This isomorphism
    should be in mathlib somewhere, but if you can't find it, this is how you would
    prove it by hand:
    -/
    let e : pullback (pullback.fst f g) (𝒱.f i) ≅
        pullback (pullback.snd f (𝒰.f i)) (pullback.snd g (𝒰.f i)) :=
      { hom :=
          -- We apply the universal property of the fibre product multiple times.
          pullback.lift (pullback.lift (pullback.fst _ _ ≫ pullback.fst _ _)
          (pullback.snd _ _ ≫ pullback.snd _ _) (by simp [pullback.condition, 𝒱]))
          (pullback.lift (pullback.fst _ _ ≫ pullback.snd _ _)
          (pullback.snd _ _ ≫ pullback.snd _ _)
          (by simp [𝒱, ← pullback.condition, pullback.condition_assoc]))
          (by simp)
        inv := pullback.lift
          (pullback.lift
            (pullback.fst _ _ ≫ pullback.fst _ _)
            (pullback.snd _ _ ≫ pullback.fst _ _)
            (by simp [pullback.condition, pullback.condition_assoc]))
            (pullback.fst _ _) (by simp [𝒱])
        hom_inv_id := by
          -- This is the uniqueness part of the universal property of the fibre product.
          apply pullback.hom_ext
          · apply pullback.hom_ext <;> simp
          · apply pullback.hom_ext <;> simp [𝒱, pullback.condition]
        inv_hom_id := by
          apply pullback.hom_ext
          · apply pullback.hom_ext <;> simp
          · apply pullback.hom_ext <;> simp [pullback.condition] }
    -- We check some diagram commutes. Note that this is mostly automatic.
    have heq : pullback.snd (pullback.fst f g) (𝒱.f i) = e.hom ≫ pullback.fst _ _ := by
      apply pullback.hom_ext <;> simp [e, pullback.condition, 𝒱]
    have _ : IsIso e.hom := e.isIso_hom
    -- We rewrite with the diagram identity and use that integral is invariant under isomorphisms.
    rw [heq, cancel_left_of_respectsIso (P := @IsIntegralHom)]
    -- Now we have massaged everything into a form where we can apply the result we are trying to
    -- prove in the case where `S` is the affine scheme `Uᵢ = Spec Rᵢ`.
    apply this
    · -- Integral is stable under restriction to an open subset on the target.
      apply IsZariskiLocalAtTarget.of_isPullback (iY := 𝒰.f i)
      · apply IsPullback.of_hasPullback _ _
      · assumption
    · exact ⟨_, rfl⟩
  -- Now obtain such a commutative ring `R` such that `S = Spec R`, ...
  obtain ⟨R, hR⟩ := hS
  -- ... and replace `S` everywhere by `Spec R`. From now on, we forget about `S`.
  subst hR
  -- We do the same procedure for `X` now.
  wlog hX : ∃ S, X = Spec S
  · let 𝒰 : X.OpenCover := X.affineCover
    rw [IsZariskiLocalAtTarget.iff_of_openCover (P := @IsIntegralHom) 𝒰]
    intro i
    simp [Scheme.Cover.pullbackHom]
    have heq : pullback.snd (pullback.fst f g) (𝒰.f i) =
        (pullbackSymmetry _ _).hom ≫ (pullbackRightPullbackFstIso _ _ _).hom ≫
        pullback.fst (𝒰.f i ≫ f) g := by simp
    rw [heq, cancel_left_of_respectsIso (P := @IsIntegralHom),
      cancel_left_of_respectsIso (P := @IsIntegralHom)]
    apply this
    · assumption
    · exact ⟨_, rfl⟩
  obtain ⟨S, hS⟩ := hX
  subst hS
  -- Since `Spec` is fully faithful, we may also replace the map `f : Spec S ⟶ Spec R` by
  -- the map induced by a ring homomorphism `R ⟶ S`.
  obtain ⟨φ, hφ⟩ := Spec.map_surjective f
  subst hφ
  -- Now we also replace `Y` by `Spec T` for some `T`.
  -- Note that we already know that `Y` is affine, but to pass to commutative algebra, it is
  -- more convenient to have `Y` be *equal* to `Spec T` for some `T`.
  wlog hY : ∃ T, Y = Spec T
  · have _ : IsAffine Y := by apply isAffine_of_isAffineHom g
    -- The tricks are always the same. We assert some diagram commutes that involves
    -- some auxiliary isomorphism and automation can prove it commutes.
    have heq : pullback.fst (Spec.map φ) g =
        (asIso (pullback.map _ _ _ _ (𝟙 _) Y.isoSpec.hom (𝟙 _) (by simp) (by simp))).hom ≫
          pullback.fst (Spec.map φ) (Y.isoSpec.inv ≫ g) := by
      simp
    -- We then use invariance under isomorphisms and conclude.
    rw [heq, cancel_left_of_respectsIso (P := @IsIntegralHom)]
    apply this
    · rw [cancel_left_of_respectsIso (P := @IsIntegralHom)]
      assumption
    · exact ⟨_, rfl⟩
  obtain ⟨T, hT⟩ := hY
  subst hT
  -- Again, replace `g` by the map induced by a ring homomorphism `ψ`.
  obtain ⟨ψ, hψ⟩ := Spec.map_surjective g
  subst hψ
  /-
  For Lean a ring homomorphism `R →+* S` is *not* the same as an `R`-algebra structure on `S`.
  Since usually commutative algebra statements are formulated in the language of algebras,
  we want to translate the goal into a goal about algebras instead of ring homomorphisms.

  `algebraize [φ.hom]` says that we want to consider `S` as an `R`-algebra via the ring homomorphism
  `φ.hom`.
  -/
  algebraize [φ.hom, ψ.hom]
  -- The isomorphism `Spec S ×[Spec R] Spec T ≅ Spec (S ⊗[R] T)` together with ...
  let e : pullback (Spec.map φ) (Spec.map ψ) ≅ Spec (.of (S ⊗[R] T)) := pullbackSpecIso _ _ _
  -- ... some commutative diagram.
  have heq : pullback.fst (Spec.map φ) (Spec.map ψ) =
      e.hom ≫ Spec.map (CommRingCat.ofHom <| algebraMap _ _) := by
    simp [e, RingHom.algebraMap_toAlgebra]
  -- Again use that integral is invariant under isomorphisms.
  rw [heq, cancel_left_of_respectsIso (P := @IsIntegralHom)]
  -- The final step we need to apply is the lemma that says `Spec S ⟶ Spec R` is
  -- integral if and only if `R ⟶ S` is an integral ring homomorphism.
  rw [HasAffineProperty.SpecMap_iff_of_affineAnd (P := @IsIntegralHom)
      (Q := RingHom.IsIntegral)] at hg ⊢
  · dsimp
    rw [algebraMap_isIntegral_iff]
    have : Algebra.IsIntegral R T := by
      rw [← algebraMap_isIntegral_iff]
      apply hg
    /-
    After 100 lines of reduction, the remaining goal is that `S ⊗[R] T` is an integral
    `S`-algebra if `T` is an integral `R`-algebra.

    The proof is `infer_instance` which says: This result already exists in the library, so
    please automatically insert the lemma.
    -/
    infer_instance
  · infer_instance
  · apply RingHom.isIntegral_respectsIso
  · infer_instance
  · apply RingHom.isIntegral_respectsIso

/-
Note: The above proof is purely formal (the only non formal thing is happening in one of the very
last steps of the proof where we show that `S ⊗[R] T` is `S`-integral).

The correct way to prove such a statement is by completely abstracting away the specific properties
at hand and to turn the proof into a general lemma about certain properties
associated to certain properties of ring homomorphisms are stable under base change if
it holds for the property of ring homomorphisms.

The relevant lemma in this case is the following:
-/
#check HasAffineProperty.affineAnd_isStableUnderBaseChange
