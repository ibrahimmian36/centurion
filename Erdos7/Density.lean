/-
Copyright (c) 2026 Millennium Research. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Millennium Research (Ibby Mian), with Claude
-/
import Mathlib

/-!
# The Density Lemma for covering systems

A *covering class* is a pair `(d, r) : ℕ × ℕ` denoting `{x : x % d = r}`.
Here every modulus `d` divides a common period `N`, so the whole system is
determined by its behaviour on `{0, 1, ..., N-1}`.

Main results:
* `card_filter_mod_le`  — a single class meets `[0, N)` in at most `N / d` points.
* `covering_density`    — if the classes cover `[0, N)` then `N ≤ ∑ N / dᵢ`.
* `covering_density_rat`— the same, as `1 ≤ ∑ 1 / dᵢ` over `ℚ`.
* `covering_density_zmod` — the `ZMod N` phrasing of `covering_density`.
* `sum_divisors_ge_of_covering` — with *distinct* moduli all `> 1`, `2 * N ≤ σ₁ N`.
* `not_deficient_of_covering`   — restatement: `N` is perfect or abundant.

The last two are the Erdős-7 targeting lemma: any covering system whose moduli
are distinct divisors of `N`, each exceeding `1`, forces `N` to be
abundant-or-perfect. This is what restricts the search for an *odd* covering
system to odd abundant `N`.
-/

/-- The residue class `r mod d` meets `[0, N)` in at most `N / d` points.
Requires `d ∣ N` (for `d = 0` this forces `N = 0` and both sides vanish). -/
theorem card_filter_mod_le (N d r : ℕ) (hd : d ∣ N) :
    ((Finset.range N).filter (fun x => x % d = r)).card ≤ N / d := by
  classical
  rw [← Finset.card_range (N / d)]
  refine Finset.card_le_card_of_injOn (fun x => x / d) ?_ ?_
  · intro x hx
    simp only [Finset.mem_coe, Finset.mem_filter, Finset.mem_range] at hx ⊢
    exact Nat.div_lt_div_of_lt_of_dvd hd hx.1
  · intro x hx y hy hxy
    simp only [Finset.mem_coe, Finset.mem_filter, Finset.mem_range] at hx hy
    have hxy' : x / d = y / d := hxy
    have hx' := Nat.div_add_mod x d
    have hy' := Nat.div_add_mod y d
    rw [hx.2] at hx'
    rw [hy.2, ← hxy'] at hy'
    exact hx'.symm.trans hy'

/-- **Density lemma.** If the classes `(dᵢ, rᵢ)` in `S`, with every `dᵢ ∣ N`,
cover every `x < N`, then `N ≤ ∑ᵢ N / dᵢ`. -/
theorem covering_density (N : ℕ) (S : Finset (ℕ × ℕ))
    (hdvd : ∀ p ∈ S, p.1 ∣ N)
    (hcov : ∀ x < N, ∃ p ∈ S, x % p.1 = p.2) :
    N ≤ ∑ p ∈ S, N / p.1 := by
  classical
  have hsub : Finset.range N ⊆
      S.biUnion (fun p => (Finset.range N).filter (fun x => x % p.1 = p.2)) := by
    intro x hx
    rw [Finset.mem_range] at hx
    obtain ⟨p, hpS, hp⟩ := hcov x hx
    refine Finset.mem_biUnion.2 ⟨p, hpS, ?_⟩
    simp only [Finset.mem_filter, Finset.mem_range]
    exact ⟨hx, hp⟩
  calc N = (Finset.range N).card := (Finset.card_range N).symm
    _ ≤ (S.biUnion (fun p => (Finset.range N).filter (fun x => x % p.1 = p.2))).card :=
        Finset.card_le_card hsub
    _ ≤ ∑ p ∈ S, ((Finset.range N).filter (fun x => x % p.1 = p.2)).card :=
        Finset.card_biUnion_le
    _ ≤ ∑ p ∈ S, N / p.1 :=
        Finset.sum_le_sum (fun p hp => card_filter_mod_le N p.1 p.2 (hdvd p hp))

/-- Rational form of the density lemma: `1 ≤ ∑ᵢ 1 / dᵢ`. -/
theorem covering_density_rat {N : ℕ} (hN : 0 < N) (S : Finset (ℕ × ℕ))
    (hdvd : ∀ p ∈ S, p.1 ∣ N)
    (hcov : ∀ x < N, ∃ p ∈ S, x % p.1 = p.2) :
    (1 : ℚ) ≤ ∑ p ∈ S, (1 : ℚ) / (p.1 : ℚ) := by
  have key := covering_density N S hdvd hcov
  have hNQ : (0 : ℚ) < (N : ℚ) := by exact_mod_cast hN
  have h1 : (N : ℚ) ≤ ∑ p ∈ S, (((N / p.1 : ℕ) : ℚ)) := by exact_mod_cast key
  have h2 : ∑ p ∈ S, (((N / p.1 : ℕ) : ℚ)) ≤ ∑ p ∈ S, (N : ℚ) / (p.1 : ℚ) :=
    Finset.sum_le_sum (fun p _ => Nat.cast_div_le)
  have h3 : ∑ p ∈ S, (N : ℚ) / (p.1 : ℚ) = (N : ℚ) * ∑ p ∈ S, (1 : ℚ) / (p.1 : ℚ) := by
    rw [Finset.mul_sum]
    exact Finset.sum_congr rfl (fun p _ => by rw [mul_one_div])
  have hfin : (N : ℚ) * 1 ≤ (N : ℚ) * (∑ p ∈ S, (1 : ℚ) / (p.1 : ℚ)) := by
    rw [mul_one, ← h3]; exact h1.trans h2
  exact le_of_mul_le_mul_left hfin hNQ

set_option linter.unusedVariables false in
/-- `ZMod N` phrasing: covering all of `ZMod N` gives the same density bound.
`hN` is kept in the signature for callers' convenience even though the proof
does not consume it (for `N = 0` the conclusion is trivial). -/
theorem covering_density_zmod {N : ℕ} (hN : 0 < N) (S : Finset (ℕ × ℕ))
    (hdvd : ∀ p ∈ S, p.1 ∣ N)
    (hcov : ∀ x : ZMod N, ∃ p ∈ S, (ZMod.val x) % p.1 = p.2) :
    N ≤ ∑ p ∈ S, N / p.1 := by
  haveI : NeZero N := ⟨hN.ne'⟩
  refine covering_density N S hdvd ?_
  intro x hx
  have := hcov (x : ZMod N)
  rwa [ZMod.val_natCast_of_lt hx] at this

/-- **Erdős-7 targeting lemma.** A covering system whose moduli are *distinct*
divisors of `N`, each `> 1`, forces `2 * N ≤ σ₁ N`: `N` is abundant or perfect. -/
theorem sum_divisors_ge_of_covering {N : ℕ} (hN : 0 < N) (S : Finset (ℕ × ℕ))
    (hdvd : ∀ p ∈ S, p.1 ∣ N) (hone : ∀ p ∈ S, 1 < p.1)
    (hinj : Set.InjOn Prod.fst (S : Set (ℕ × ℕ)))
    (hcov : ∀ x < N, ∃ p ∈ S, x % p.1 = p.2) :
    2 * N ≤ ∑ d ∈ N.divisors, d := by
  classical
  have hN0 : N ≠ 0 := hN.ne'
  have hsumD : ∑ d ∈ S.image Prod.fst, N / d = ∑ p ∈ S, N / p.1 := Finset.sum_image hinj
  have hkey : N ≤ ∑ d ∈ S.image Prod.fst, N / d := by
    rw [hsumD]; exact covering_density N S hdvd hcov
  have hsub : S.image Prod.fst ⊆ N.divisors.erase 1 := by
    intro d hd
    rw [Finset.mem_image] at hd
    obtain ⟨p, hpS, rfl⟩ := hd
    rw [Finset.mem_erase, Nat.mem_divisors]
    exact ⟨(hone p hpS).ne', hdvd p hpS, hN0⟩
  have hmono : ∑ d ∈ S.image Prod.fst, N / d ≤ ∑ d ∈ N.divisors.erase 1, N / d :=
    Finset.sum_le_sum_of_subset hsub
  have h1mem : (1 : ℕ) ∈ N.divisors := Nat.one_mem_divisors.2 hN0
  have hsplit : N / 1 + ∑ d ∈ N.divisors.erase 1, N / d = ∑ d ∈ N.divisors, N / d :=
    Finset.add_sum_erase _ _ h1mem
  have hdd : ∑ d ∈ N.divisors, N / d = ∑ d ∈ N.divisors, d :=
    Nat.sum_div_divisors N (fun d => d)
  omega

/-- Restatement of `sum_divisors_ge_of_covering`: such an `N` is not deficient. -/
theorem not_deficient_of_covering {N : ℕ} (hN : 0 < N) (S : Finset (ℕ × ℕ))
    (hdvd : ∀ p ∈ S, p.1 ∣ N) (hone : ∀ p ∈ S, 1 < p.1)
    (hinj : Set.InjOn Prod.fst (S : Set (ℕ × ℕ)))
    (hcov : ∀ x < N, ∃ p ∈ S, x % p.1 = p.2) :
    ¬ N.Deficient := by
  have h := sum_divisors_ge_of_covering hN S hdvd hone hinj hcov
  have hs : ∑ i ∈ N.divisors, i = ∑ i ∈ N.properDivisors, i + N :=
    Nat.sum_divisors_eq_sum_properDivisors_add_self
  rw [Nat.Deficient, not_lt]
  omega


/-! ## BRIDGE (new): covering all of ℤ ⇒ density ≥ 1, indexed by any finite type. -/

theorem covering_density_ge_one
    {ι : Type} [Fintype ι] (n : ι → ℕ) (a : ι → ℤ)
    (hpos : ∀ i, 0 < n i)
    (hcov : ∀ x : ℤ, ∃ i, (n i : ℤ) ∣ (x - a i)) :
    (1 : ℚ) ≤ ∑ i, (1 : ℚ) / n i := by
  classical
  set N := Finset.univ.lcm n with hNdef
  have hdvdN : ∀ i, n i ∣ N := fun i => Finset.dvd_lcm (Finset.mem_univ i)
  have hN0 : 0 < N := by
    refine Nat.pos_of_ne_zero ?_
    rw [hNdef, Ne, Finset.lcm_eq_zero_iff]
    rintro ⟨x, -, hx⟩
    exact (hpos x).ne' hx
  set r : ι → ℕ := fun i => ((a i) % (n i : ℤ)).toNat with hrdef
  set S : Finset (ℕ × ℕ) := Finset.univ.image (fun i => (n i, r i)) with hSdef
  have hdvd : ∀ p ∈ S, p.1 ∣ N := by
    intro p hp
    obtain ⟨i, -, rfl⟩ := Finset.mem_image.mp hp
    exact hdvdN i
  have hcov' : ∀ x < N, ∃ p ∈ S, x % p.1 = p.2 := by
    intro x _
    obtain ⟨i, hi⟩ := hcov (x : ℤ)
    refine ⟨(n i, r i), Finset.mem_image.2 ⟨i, Finset.mem_univ i, rfl⟩, ?_⟩
    have h1 : (a i) % (n i : ℤ) = (x : ℤ) % (n i : ℤ) := Int.modEq_iff_dvd.mpr hi
    have h2 : ((x : ℤ)) % (n i : ℤ) = ((x % n i : ℕ) : ℤ) := by
      rw [Int.natCast_mod]
    change x % n i = r i
    rw [hrdef]
    simp only [h1, h2, Int.toNat_natCast]
  have key := covering_density_rat hN0 S hdvd hcov'
  have hle : ∑ p ∈ S, (1 : ℚ) / (p.1 : ℚ) ≤ ∑ i, (1 : ℚ) / (n i : ℚ) := by
    rw [hSdef]
    exact Finset.sum_image_le_of_nonneg (fun u _ => by positivity)
  linarith

/-! ### Anti-vacuity: the hypotheses are satisfiable

Erdős' smallest distinct covering system `{0 mod 2, 0 mod 3, 1 mod 4, 5 mod 6, 7 mod 12}`
(period `N = 12`) meets every hypothesis above, so none of the theorems is vacuous. -/

/-- The classic 5-class system really does cover, and `decide` sees it. -/
example : ∀ x < 12, ∃ p ∈ ({(2,0),(3,0),(4,1),(6,5),(12,7)} : Finset (ℕ × ℕ)),
    x % p.1 = p.2 := by decide

/-- Instantiating the density lemma at that system. -/
example : 12 ≤ ∑ p ∈ ({(2,0),(3,0),(4,1),(6,5),(12,7)} : Finset (ℕ × ℕ)), 12 / p.1 :=
  covering_density 12 _ (by decide) (by decide)

/-- Instantiating the targeting lemma: it correctly reports that `12` is
abundant-or-perfect (`σ₁ 12 = 28 ≥ 24`). -/
example : 2 * 12 ≤ ∑ d ∈ (12 : ℕ).divisors, d := by
  refine sum_divisors_ge_of_covering (N := 12) (by norm_num)
    ({(2,0),(3,0),(4,1),(6,5),(12,7)} : Finset (ℕ × ℕ))
    (by decide) (by decide) ?_ (by decide)
  have key : ∀ a ∈ ({(2,0),(3,0),(4,1),(6,5),(12,7)} : Finset (ℕ × ℕ)),
      ∀ b ∈ ({(2,0),(3,0),(4,1),(6,5),(12,7)} : Finset (ℕ × ℕ)),
      a.1 = b.1 → a = b := by decide
  exact fun a ha b hb hab => key a (Finset.mem_coe.1 ha) b (Finset.mem_coe.1 hb) hab
