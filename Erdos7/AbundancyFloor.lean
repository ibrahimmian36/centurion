/-
Copyright (c) 2026 Millennium Research. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Millennium Research (Ibby Mian), with Claude
-/
import Erdos7.Density

set_option maxRecDepth 100000
set_option maxHeartbeats 4000000

/-! # The abundancy floor: no odd `N < 945` is abundant. -/

theorem abundancy_floor_945 :
    ∀ n < 945, n % 2 = 1 → ∑ d ∈ Nat.divisors n, d < 2 * n := by
  decide +kernel

/-! # Bridging step: `∑_{d ∣ N, d > 1} 1/d = σ₁(N)/N - 1`. -/

open Finset in
theorem sum_inv_divisors_eq (N : ℕ) (hN : N ≠ 0) :
    ∑ d ∈ N.divisors, (1 : ℚ) / d = (∑ d ∈ N.divisors, (d : ℚ)) / N := by
  have h := Nat.sum_div_divisors N (fun d => (d : ℚ) / N)
  rw [Finset.sum_div, ← h]
  refine Finset.sum_congr rfl fun d hd => ?_
  obtain ⟨hdvd, -⟩ := Nat.mem_divisors.mp hd
  have hd0 : d ≠ 0 := by rintro rfl; exact hN (Nat.eq_zero_of_zero_dvd hdvd)
  have hcast : ((N / d : ℕ) : ℚ) = (N : ℚ) / d := by
    rw [Nat.cast_div hdvd (Nat.cast_ne_zero.mpr hd0)]
  rw [hcast]
  have hNq : (N : ℚ) ≠ 0 := Nat.cast_ne_zero.mpr hN
  have hdq : (d : ℚ) ≠ 0 := Nat.cast_ne_zero.mpr hd0
  field_simp

open Finset in
theorem sum_inv_divisors_erase_one (N : ℕ) (hN : N ≠ 0) :
    ∑ d ∈ N.divisors.erase 1, (1 : ℚ) / d
      = (∑ d ∈ N.divisors, (d : ℚ)) / N - 1 := by
  have h1 : (1 : ℕ) ∈ N.divisors := Nat.one_mem_divisors.mpr hN
  have h := Finset.add_sum_erase N.divisors (fun d => (1 : ℚ) / d) h1
  rw [← sum_inv_divisors_eq N hN, ← h]
  push_cast
  ring

open Finset in
theorem sum_inv_le_abundancy (N : ℕ) (hN : N ≠ 0) (S : Finset ℕ)
    (hS : S ⊆ N.divisors.erase 1) :
    ∑ d ∈ S, (1 : ℚ) / d ≤ (∑ d ∈ N.divisors, (d : ℚ)) / N - 1 := by
  rw [← sum_inv_divisors_erase_one N hN]
  refine Finset.sum_le_sum_of_subset_of_nonneg hS fun d _ _ => ?_
  positivity

/-! # Assembled headline. -/

open Finset in
theorem odd_covering_lcm_ge_945
    {ι : Type} [Fintype ι]
    (n : ι → ℕ) (a : ι → ℤ)
    (hgt : ∀ i, 1 < n i) (hodd : ∀ i, Odd (n i))
    (hinj : Function.Injective n)
    (hcov : ∀ x : ℤ, ∃ i, (n i : ℤ) ∣ (x - a i)) :
    945 ≤ Finset.univ.lcm n := by
  classical
  set L := Finset.univ.lcm n with hLdef
  have hpos : ∀ i, 0 < n i := fun i => lt_trans Nat.zero_lt_one (hgt i)
  have hdvd : ∀ i, n i ∣ L := fun i => Finset.dvd_lcm (Finset.mem_univ i)
  have hL0 : L ≠ 0 := by
    rw [hLdef, Ne, Finset.lcm_eq_zero_iff]
    rintro ⟨x, -, hx⟩
    exact (hpos x).ne' hx
  have hsub : (Finset.univ.image n) ⊆ L.divisors.erase 1 := by
    intro d hd
    obtain ⟨i, -, rfl⟩ := Finset.mem_image.mp hd
    exact Finset.mem_erase.mpr ⟨(hgt i).ne', Nat.mem_divisors.mpr ⟨hdvd i, hL0⟩⟩
  have hdens : (1 : ℚ) ≤ ∑ i, (1 : ℚ) / n i := covering_density_ge_one n a hpos hcov
  have himg : ∑ d ∈ Finset.univ.image n, (1 : ℚ) / d = ∑ i, (1 : ℚ) / n i :=
    Finset.sum_image (fun x _ y _ h => hinj h)
  have hbridge := sum_inv_le_abundancy L hL0 (Finset.univ.image n) hsub
  rw [himg] at hbridge
  have hLq : (0 : ℚ) < (L : ℚ) := by exact_mod_cast Nat.pos_of_ne_zero hL0
  have h2 : (2 : ℚ) ≤ (∑ d ∈ L.divisors, (d : ℚ)) / L := by linarith
  have hcancel : ((∑ d ∈ L.divisors, (d : ℚ)) / (L : ℚ)) * L
      = ∑ d ∈ L.divisors, (d : ℚ) := by field_simp
  have hm := mul_le_mul_of_nonneg_right h2 hLq.le
  rw [hcancel] at hm
  have habund : 2 * L ≤ ∑ d ∈ L.divisors, d := by
    have hc : ((∑ d ∈ L.divisors, d : ℕ) : ℚ) = ∑ d ∈ L.divisors, (d : ℚ) := by push_cast; ring
    rw [← hc] at hm
    exact_mod_cast hm
  have hLodd : L % 2 = 1 := by
    rcases Nat.even_or_odd L with he | ho
    · exfalso
      have hLm : L % 2 = 0 := Nat.even_iff.mp he
      have h2L : (2 : ℕ) ∣ L := by omega
      have hLp : L ∣ ∏ i, n i :=
        Finset.lcm_dvd fun i _ => Finset.dvd_prod_of_mem n (Finset.mem_univ i)
      have hprod : Odd (∏ i, n i) :=
        Finset.prod_induction _ Odd (fun x y hx hy => hx.mul hy) odd_one (fun i _ => hodd i)
      rw [Nat.odd_iff] at hprod
      have : (2 : ℕ) ∣ ∏ i, n i := h2L.trans hLp
      omega
    · exact Nat.odd_iff.mp ho
  rcases Nat.lt_or_ge L 945 with hlt | hge
  · have hfloor := abundancy_floor_945 L hlt hLodd
    omega
  · exact hge
