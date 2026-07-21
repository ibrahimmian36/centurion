import Mathlib

-- Pair 18 formalization, exactly as given (proof replaced to TEST triviality).
-- English: if f factors as product of three IRREDUCIBLE QUADRATIC polynomials Q₁,Q₂,Q₃
-- in k[x,y], then f is written in the specific "form (A)".
-- Lean conclusion: ∃ a b c d e l₁ l₂ l₃, f = l₁ * l₂ * l₃

-- CLAIM UNDER TEST: the goal is trivially provable from hf alone, with a..e arbitrary,
-- and l₁,l₂,l₃ := Q₁,Q₂,Q₃. If this proof closes WITHOUT `sorry`, the conclusion
-- encodes essentially nothing beyond hf (it is vacuous re: irreducibility/quadratic/form A).
theorem factored_into_three_irreducible_quadratics
    (k : Type*) [Field k]
    (f Q₁ Q₂ Q₃ : MvPolynomial (Fin 2) k)
    (hQ₁ : Irreducible Q₁)
    (hQ₂ : Irreducible Q₂)
    (hQ₃ : Irreducible Q₃)
    (hf : f = Q₁ * Q₂ * Q₃) :
    ∃ (a b c d e : k) (l₁ l₂ l₃ : MvPolynomial (Fin 2) k),
      f = l₁ * l₂ * l₃ :=
  -- witnesses: a..e all 0 (arbitrary, unused); l₁,l₂,l₃ := Q₁,Q₂,Q₃
  ⟨0, 0, 0, 0, 0, Q₁, Q₂, Q₃, hf⟩

-- Even STRONGER: the hypotheses hQ₁,hQ₂,hQ₃ (irreducibility) are not needed at all.
-- And the conclusion is provable even when Q's are NOT irreducible and NOT quadratic:
theorem conclusion_does_not_need_irreducible_or_quadratic
    (k : Type*) [Field k]
    (f Q₁ Q₂ Q₃ : MvPolynomial (Fin 2) k)
    (hf : f = Q₁ * Q₂ * Q₃) :
    ∃ (a b c d e : k) (l₁ l₂ l₃ : MvPolynomial (Fin 2) k),
      f = l₁ * l₂ * l₃ :=
  ⟨0, 0, 0, 0, 0, Q₁, Q₂, Q₃, hf⟩

-- Even STRONGER still: ANY f over a field admits SOME factorization into 3 factors
-- (f = f * 1 * 1), so the conclusion alone (dropping hf entirely) is essentially trivial too.
theorem conclusion_holds_for_any_f
    (k : Type*) [Field k]
    (f : MvPolynomial (Fin 2) k) :
    ∃ (a b c d e : k) (l₁ l₂ l₃ : MvPolynomial (Fin 2) k),
      f = l₁ * l₂ * l₃ :=
  ⟨0, 0, 0, 0, 0, f, 1, 1, by simp⟩
