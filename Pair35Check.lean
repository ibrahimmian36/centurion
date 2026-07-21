import Mathlib

-- The cited defect: φ : SX_g →ₗ[F] SX_GF is an ARBITRARY linear input, and the conclusion
-- `Function.Surjective φ` is asserted with no hypothesis pinning φ to the natural map.
-- A universally-quantified "every linear map is surjective" is FALSE: the zero map witnesses it.

-- (1) The zero linear map between nonzero spaces is NOT surjective.
example : ¬ Function.Surjective (0 : ℝ →ₗ[ℝ] ℝ) := by
  intro h
  obtain ⟨x, hx⟩ := h 1
  simp at hx

-- (2) Mini-model of the EXACT conclusion shape, quantified over arbitrary φ ψ (as in the
--     theorem), with concrete nonzero coinvariant spaces. The claim is refutable.
example :
    ¬ (∀ (SX_g SX_GF : Type) [AddCommGroup SX_g] [AddCommGroup SX_GF]
         [Module ℝ SX_g] [Module ℝ SX_GF]
         (φ : SX_g →ₗ[ℝ] SX_GF), Function.Surjective φ) := by
  intro H
  have hsurj : Function.Surjective (0 : ℝ →ₗ[ℝ] ℝ) := H ℝ ℝ 0
  obtain ⟨x, hx⟩ := hsurj 1
  simp at hx

-- (3) For contrast: the FAITHFUL encoding would constrain φ. E.g. give the natural
--     factorization hypothesis (φ ∘ π₁ = π₂) together with surjectivity of π₂; THEN φ is
--     surjective. Without that hypothesis the theorem is just false.
example {SX SX_g SX_GF : Type*}
    [AddCommGroup SX] [AddCommGroup SX_g] [AddCommGroup SX_GF]
    [Module ℝ SX] [Module ℝ SX_g] [Module ℝ SX_GF]
    (π₁ : SX →ₗ[ℝ] SX_g) (π₂ : SX →ₗ[ℝ] SX_GF)
    (φ : SX_g →ₗ[ℝ] SX_GF)
    (hfact : ∀ x, φ (π₁ x) = π₂ x)
    (hπ₂ : Function.Surjective π₂) :
    Function.Surjective φ := by
  intro y
  obtain ⟨x, rfl⟩ := hπ₂ y
  exact ⟨π₁ x, hfact x⟩
