import Mathlib

-- algebraMap from a CharZero field to ℂ is injective (so image-equality captures "x is of that form")
example {K : Type*} [Field K] [Algebra K ℂ] :
    Function.Injective (algebraMap K ℂ) := by
  exact RingHom.injective _

-- The preperiodic off-by-one: m,k≥1 form vs m,k≥0 form are equivalent.
-- Show the ≥0 form implies the ≥1 form (the nontrivial direction) for a general self-map f.
example {α : Type*} (f : α → α) (x : α)
    (h : ∃ m k : ℕ, m ≠ k ∧ f^[m] x = f^[k] x) :
    ∃ m k : ℕ, 0 < m ∧ 0 < k ∧ m ≠ k ∧ f^[m] x = f^[k] x := by
  obtain ⟨m, k, hmk, heq⟩ := h
  refine ⟨m + 1, k + 1, Nat.succ_pos _, Nat.succ_pos _, by omega, ?_⟩
  rw [Function.iterate_succ', Function.iterate_succ']
  simp only [Function.comp_apply]
  rw [heq]

-- Conversely ≥1 form trivially gives the ≥0 (general) form.
example {α : Type*} (f : α → α) (x : α)
    (h : ∃ m k : ℕ, 0 < m ∧ 0 < k ∧ m ≠ k ∧ f^[m] x = f^[k] x) :
    ∃ m k : ℕ, m ≠ k ∧ f^[m] x = f^[k] x := by
  obtain ⟨m, k, _, _, hmk, heq⟩ := h
  exact ⟨m, k, hmk, heq⟩
