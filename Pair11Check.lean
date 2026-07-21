import Mathlib

set_option maxHeartbeats 1000000

-- ============================================================================
-- Pair 11 faithfulness check.
-- Informal: χ ∈ F_{p^2}^× with |χ| ∉ {1,2} and |χ| ∈ D(p±1). Then EXACTLY ONE
-- of ι_{p±1}(χ), ι_{p±1}(χ⁻¹) is in the LOWER HALF.
-- Lean conclusion under test:
--   Xor' (orderOf χ < orderOf χ / 2) (orderOf (χ⁻¹) < orderOf (χ⁻¹) / 2)
-- ============================================================================

-- CLAIM A: `n < n / 2` (Nat division) is FALSE for EVERY n : ℕ.
theorem A_nat_lt_half_always_false : ∀ n : ℕ, ¬ (n < n / 2) := by
  intro n h
  have : n / 2 ≤ n := Nat.div_le_self n 2
  omega

-- CLAIM B: orderOf χ⁻¹ = orderOf χ ALWAYS (any group element), so the two
-- disjuncts of the Xor' are the SAME proposition up to this rewrite.
theorem B_orderOf_inv_eq {G : Type*} [Group G] (x : G) :
    orderOf x⁻¹ = orderOf x := orderOf_inv x

-- CLAIM C (the punchline): The EXACT conclusion of the theorem is PROVABLY FALSE
-- for every χ. I.e. the statement is unprovable / vacuous: ¬ (the goal).
-- This uses the units group (ZMod (p^2))ˣ exactly as in the formalization.
theorem C_conclusion_is_false
    {p : ℕ} [Fact p.Prime] (χ : (ZMod (p^2))ˣ) :
    ¬ Xor' (orderOf χ < orderOf χ / 2) (orderOf (χ⁻¹) < orderOf (χ⁻¹) / 2) := by
  rw [Xor']
  rintro (⟨h, _⟩ | ⟨h, _⟩)
  · exact A_nat_lt_half_always_false _ h
  · exact A_nat_lt_half_always_false _ h

-- CLAIM E: After rewriting with orderOf_inv, the conclusion is literally `Xor' P P`,
-- which mathlib proves equals False via `xor_self`.
theorem E_reduces_to_xor_self
    {p : ℕ} [Fact p.Prime] (χ : (ZMod (p^2))ˣ) :
    Xor' (orderOf χ < orderOf χ / 2) (orderOf (χ⁻¹) < orderOf (χ⁻¹) / 2)
      = Xor' (orderOf χ < orderOf χ / 2) (orderOf χ < orderOf χ / 2) := by
  rw [orderOf_inv]

theorem E2_xor_self_is_false (P : Prop) : Xor' P P = False := xor_self P

-- ============================================================================
-- CLAIM F: domain mismatch. ZMod (p^2) is NOT a field (p is a zero-divisor),
-- and its unit group has order p*(p-1), NOT p^2 - 1 = card(F_{p^2}^×).
-- Concretely at p = 3:  card (ZMod 9)ˣ = 6 = 3*2, while card F_9^× = 8.
-- ============================================================================
theorem F_units_card_p3 : Fintype.card (ZMod 9)ˣ = 6 := by decide

theorem F_field_card_p3 : Nat.card (GaloisField 3 2) = 9 :=
  GaloisField.card 3 2 (by norm_num)

-- field units count = card - 1 = 8, vs ZMod 9 units count = 6 above. Hence the
-- two multiplicative groups are NOT isomorphic — different domains.
theorem F_field_units_card_p3 : Nat.card (GaloisField 3 2)ˣ = 8 := by
  rw [Nat.card_units, F_field_card_p3]

-- ZMod 9 is NOT a field (3 is a nonzero non-unit / zero divisor: 3 * 3 = 0).
theorem F_zmod9_not_field : ¬ IsField (ZMod 9) := by
  intro h
  -- in a field every nonzero element is a unit; but 3 is nonzero and 3*3 = 0
  have h3 : (3 : ZMod 9) ≠ 0 := by decide
  obtain ⟨inv, hinv⟩ := h.mul_inv_cancel h3
  have : (3 : ZMod 9) * 3 = 0 := by decide
  have : (3 : ZMod 9) * 3 * inv = 0 * inv := by rw [this]
  rw [mul_assoc, hinv, mul_one, zero_mul] at this
  exact h3 this
