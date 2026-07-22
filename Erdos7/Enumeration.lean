/-
Copyright (c) 2026 Millennium Research. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Millennium Research (Ibby Mian), with Claude
-/
import Erdos7.Capacity

/-!
# The enumeration lemma and the composed headline (Erdős #7, step 5)

Step 4 (`Erdos7.Capacity`) excludes each of the 23 odd abundant-or-perfect
`N < 10000` as a covering lcm. This file supplies the missing half, that
those 23 are the only odd `L ≤ 10000` with `2 * L ≤ σ₁ L`, and composes the
two into the headline

`odd_covering_lcm_gt_10000` : any covering of `ℤ` by finitely many congruence
classes with distinct odd moduli `> 1` has `lcm > 10000`.

The enumeration is kernel-checked. The naive `decide` over `Nat.divisors` is
infeasible (measured: 152 s at bound 500) because the divisor sum routes
through `Finset`/`Multiset` quotients, which kernel reduction crawls through.
So we compute σ with a Finset-free, structurally recursive `sigmaAux`
(accumulator-style, so reduction never builds a deep pending term), scan
`[0, X]` with a Bool scanner `enumOk` that short-circuits even numbers after
a single `% 2` and list members before the σ computation, prove the scanner
sound by induction, and check ONE closed Bool equality by `decide`.

`Nat.Abundant` is not used anywhere: the target predicate is the
non-strict `2 * L ≤ σ₁ L` (abundant-or-perfect) throughout; the strict
predicate would silently exclude perfect numbers from the enumeration.
-/

/-! ## A Finset-free, kernel-computable σ (√-pairing) -/

/-- Paired-divisor scan: for each `d ≤ fuel` with `d ∣ n`, add the pair
`d + n / d` (just `d` when `d * d = n`). Structural recursion with an
accumulator; run with `fuel = √n` it visits `O(√n)` candidates at recursion
depth `≤ √n`: both the step count and the depth that made the naive linear
scan infeasible are gone. -/
def sigmaPairAux (n : ℕ) : ℕ → ℕ → ℕ
  | 0, acc => acc
  | d + 1, acc =>
    sigmaPairAux n d (acc +
      if n % (d + 1) = 0 then
        (if (d + 1) * (d + 1) = n then d + 1
         else if (d + 1) * (d + 1) < n then (d + 1) + n / (d + 1)
         else 0)
      else 0)

/-- Finset-free divisor sum for `n < 101²`: the fuel is the CONSTANT `100`,
never `Nat.sqrt`, which is defined by well-founded recursion and does
not reduce in the kernel, which would stall `decide` (measured: it did). The
`d * d` three-way guard performs the √-cutoff arithmetically instead; all
sqrt reasoning lives in the abstract correctness lemma `sigma100_eq_sigma`.
Recursion depth is a constant `100` for every argument. -/
def sigma100 (n : ℕ) : ℕ :=
  sigmaPairAux n 100 0

theorem sigmaPairAux_eq (n : ℕ) : ∀ k acc,
    sigmaPairAux n k acc = acc + ∑ d ∈ (Finset.Ico 1 (k + 1)).filter (· ∣ n),
      (if d * d = n then d else if d * d < n then d + n / d else 0) := by
  intro k
  induction k with
  | zero =>
    intro acc
    simp [sigmaPairAux]
  | succ d ih =>
    intro acc
    rw [sigmaPairAux, ih]
    have hsplit : Finset.Ico 1 (d + 1 + 1) = insert (d + 1) (Finset.Ico 1 (d + 1)) := by
      ext x
      simp only [Finset.mem_Ico, Finset.mem_insert]
      omega
    have hnotmem : (d + 1) ∉ (Finset.Ico 1 (d + 1)).filter (· ∣ n) := by
      simp [Finset.mem_filter, Finset.mem_Ico]
    rw [hsplit, Finset.filter_insert]
    by_cases hdvd : (d + 1) ∣ n
    · have hmod : n % (d + 1) = 0 := by
        obtain ⟨c, rfl⟩ := hdvd
        exact Nat.mul_mod_right _ _
      rw [if_pos hdvd, Finset.sum_insert hnotmem, if_pos hmod]
      by_cases hsq : (d + 1) * (d + 1) = n
      · rw [if_pos hsq]
        omega
      · rw [if_neg hsq]
        by_cases hlt : (d + 1) * (d + 1) < n
        · rw [if_pos hlt]
          omega
        · rw [if_neg hlt]
          omega
    · rw [if_neg hdvd, if_neg (fun h => hdvd (Nat.dvd_of_mod_eq_zero h))]
      omega

/-- `n / (n / d) = d` for a divisor `d` of a positive `n` (self-contained; the
two cancellations, nothing else). -/
theorem nat_div_div_self {d n : ℕ} (h : d ∣ n) (hn : 0 < n) : n / (n / d) = d := by
  obtain ⟨c, rfl⟩ := h
  have hd : 0 < d := by
    rcases Nat.eq_zero_or_pos d with rfl | hpos
    · simp at hn
    · exact hpos
  have hc : 0 < c := by
    rcases Nat.eq_zero_or_pos c with rfl | hpos
    · simp at hn
    · exact hpos
  rw [Nat.mul_div_cancel_left c hd, Nat.mul_comm d c, Nat.mul_div_cancel_left d hc]

/-- Generic pairing correctness: for any fuel `k` with `n < (k+1)²`, the
paired scan computes the full divisor sum: small divisors `d ≤ √n` carry
their partners `n / d` (the divisors `> √n`), the square root counted once;
the `d * d` guards cut exactly at `√n`. Stated over an ABSTRACT `k` so no
concrete fuel term is ever unfolded during elaboration (a literal `100`
here sent `whnf` into evaluating the 101-element `Ico`; measured timeout). -/
theorem sigmaPair_eq_sigma (n k : ℕ) (hn : 0 < n) (hbound : n < (k + 1) * (k + 1)) :
    sigmaPairAux n k 0 = ∑ d ∈ n.divisors, d := by
  rw [sigmaPairAux_eq, Nat.zero_add]
  set s := Nat.sqrt n with hs
  -- the three-way summand is the pair summand gated by `d * d ≤ n`
  have h3to2 : ∀ d : ℕ, (if d * d = n then d else if d * d < n then d + n / d else 0)
      = if d * d ≤ n then (if d * d = n then d else d + n / d) else 0 := by
    intro d
    rcases lt_trichotomy (d * d) n with h | h | h
    · rw [if_neg (by omega), if_pos h, if_pos (by omega), if_neg (by omega)]
    · rw [if_pos h, if_pos (by omega), if_pos h]
    · rw [if_neg (by omega), if_neg (by omega), if_neg (by omega)]
  have hgate : ∑ d ∈ (Finset.Ico 1 (k + 1)).filter (· ∣ n),
      (if d * d = n then d else if d * d < n then d + n / d else 0)
      = ∑ d ∈ ((Finset.Ico 1 (k + 1)).filter (· ∣ n)).filter (fun d => d * d ≤ n),
        (if d * d = n then d else d + n / d) := by
    have h1 : ∑ d ∈ ((Finset.Ico 1 (k + 1)).filter (· ∣ n)).filter (fun d => d * d ≤ n),
        (if d * d = n then d else d + n / d)
        = ∑ d ∈ (Finset.Ico 1 (k + 1)).filter (· ∣ n),
          if d * d ≤ n then (if d * d = n then d else d + n / d) else 0 :=
      Finset.sum_filter _ _
    rw [h1]
    apply Finset.sum_congr rfl
    intro d _
    exact h3to2 d
  rw [hgate]
  -- and that gated index set is exactly the small divisors `d ≤ √n`
  have hsmalleq : ((Finset.Ico 1 (k + 1)).filter (· ∣ n)).filter (fun d => d * d ≤ n)
      = (Finset.Ico 1 (s + 1)).filter (· ∣ n) := by
    have hsk : s < k + 1 := Nat.sqrt_lt.mpr hbound
    ext d
    simp only [Finset.mem_filter, Finset.mem_Ico]
    constructor
    · rintro ⟨⟨⟨h1, -⟩, h2⟩, h3⟩
      exact ⟨⟨h1, by have := Nat.le_sqrt.mpr h3; omega⟩, h2⟩
    · rintro ⟨⟨h1, h2⟩, h3⟩
      exact ⟨⟨⟨h1, by omega⟩, h3⟩, Nat.le_sqrt.mp (by omega)⟩
  rw [hsmalleq]
  set Small := n.divisors.filter (· ≤ s) with hSmall
  set Large := n.divisors.filter (fun d => ¬ d ≤ s) with hLarge
  set A := Small.filter (fun d => ¬ d * d = n) with hA
  have hdpos : ∀ d ∈ n.divisors, 0 < d := by
    intro d hd
    rcases Nat.eq_zero_or_pos d with rfl | hpos
    · exact absurd (Nat.eq_zero_of_zero_dvd (Nat.mem_divisors.mp hd).1) hn.ne'
    · exact hpos
  -- the scan's index set is exactly `Small`
  have hidx : (Finset.Ico 1 (s + 1)).filter (· ∣ n) = Small := by
    ext d
    simp only [hSmall, Finset.mem_filter, Finset.mem_Ico, Nat.mem_divisors]
    constructor
    · rintro ⟨⟨h1, h2⟩, h3⟩
      exact ⟨⟨h3, hn.ne'⟩, by omega⟩
    · rintro ⟨⟨h1, -⟩, h2⟩
      have hd0 : 0 < d := by
        rcases Nat.eq_zero_or_pos d with rfl | hpos
        · exact absurd (Nat.eq_zero_of_zero_dvd h1) hn.ne'
        · exact hpos
      exact ⟨⟨hd0, by omega⟩, h1⟩
  rw [hidx]
  -- peel each pair into `d` plus its partner
  have hpeel : ∑ d ∈ Small, (if d * d = n then d else d + n / d)
      = ∑ d ∈ Small, (d + (if d * d = n then 0 else n / d)) := by
    apply Finset.sum_congr rfl
    intro d _
    by_cases h : d * d = n <;> simp [h]
  rw [hpeel, Finset.sum_add_distrib]
  -- the partner sum ranges over `A`
  have htail : ∑ d ∈ Small, (if d * d = n then 0 else n / d) = ∑ d ∈ A, n / d := by
    have h1 : ∑ d ∈ A, n / d = ∑ d ∈ Small, if ¬ d * d = n then n / d else 0 := by
      rw [hA]
      exact Finset.sum_filter _ _
    rw [h1]
    apply Finset.sum_congr rfl
    intro d _
    by_cases h : d * d = n <;> simp [h]
  rw [htail]
  -- the right-hand side splits into small and large divisors
  have hdisj : Disjoint Small Large := by
    rw [hSmall, hLarge]
    exact Finset.disjoint_left.mpr fun d hd hd' => by
      have h1 := (Finset.mem_filter.mp hd).2
      have h2 := (Finset.mem_filter.mp hd').2
      exact h2 h1
  have hunion : Small ∪ Large = n.divisors := by
    rw [hSmall, hLarge]
    ext d
    simp only [Finset.mem_union, Finset.mem_filter]
    constructor
    · rintro (⟨h, -⟩ | ⟨h, -⟩) <;> exact h
    · intro h
      by_cases hle : d ≤ s
      · exact Or.inl ⟨h, hle⟩
      · exact Or.inr ⟨h, hle⟩
  have hR : ∑ d ∈ n.divisors, d = ∑ d ∈ Small, d + ∑ d ∈ Large, d := by
    rw [← Finset.sum_union hdisj, hunion]
  rw [hR]
  congr 1
  -- the bijection `d ↦ n / d : A ≃ Large`
  have hAfacts : ∀ d ∈ A, d ∣ n ∧ d ≤ s ∧ d * d ≠ n ∧ 0 < d := by
    intro d hd
    rw [hA, Finset.mem_filter, hSmall, Finset.mem_filter] at hd
    exact ⟨(Nat.mem_divisors.mp hd.1.1).1, hd.1.2, hd.2,
      hdpos d hd.1.1⟩
  have hmaps : ∀ d ∈ A, n / d ∈ Large := by
    intro d hd
    obtain ⟨hdvd, hle, hne, hd0⟩ := hAfacts d hd
    have hq0 : 0 < n / d := Nat.div_pos (Nat.le_of_dvd hn hdvd) hd0
    have hqdvd : n / d ∣ n := by
      obtain ⟨c, rfl⟩ := hdvd
      rw [Nat.mul_div_cancel_left c hd0]
      exact dvd_mul_left c d
    rw [hLarge, Finset.mem_filter, Nat.mem_divisors]
    refine ⟨⟨hqdvd, hn.ne'⟩, fun hqle => ?_⟩
    -- `d ≤ √n` and `n/d ≤ √n` force `n = d²`, contradicting `d² ≠ n`
    have hdd : d * d ≤ n := Nat.le_sqrt.mp hle
    have hqq : (n / d) * (n / d) ≤ n := Nat.le_sqrt.mp hqle
    have hmul : d * (n / d) = n := Nat.mul_div_cancel' hdvd
    have h1 : d ≤ n / d := Nat.le_of_mul_le_mul_left (by rw [hmul]; exact hdd) hd0
    have h2 : n / d ≤ d := Nat.le_of_mul_le_mul_left (by
      rw [Nat.mul_comm d (n / d)] at hmul
      rw [hmul]
      exact hqq) hq0
    have : d = n / d := le_antisymm h1 h2
    rw [← this] at hmul
    exact hne hmul
  have hinj : ∀ x ∈ A, ∀ y ∈ A, n / x = n / y → x = y := by
    intro x hx y hy hxy
    obtain ⟨hxdvd, -, -, -⟩ := hAfacts x hx
    obtain ⟨hydvd, -, -, -⟩ := hAfacts y hy
    rw [← nat_div_div_self hxdvd hn, hxy, nat_div_div_self hydvd hn]
  have himg : A.image (fun d => n / d) = Large := by
    ext b
    simp only [Finset.mem_image]
    constructor
    · rintro ⟨d, hd, rfl⟩
      exact hmaps d hd
    · intro hb
      rw [hLarge, Finset.mem_filter, Nat.mem_divisors] at hb
      obtain ⟨⟨hbdvd, -⟩, hbgt⟩ := hb
      have hb0 : 0 < b := by
        rcases Nat.eq_zero_or_pos b with rfl | hpos
        · exact absurd (Nat.eq_zero_of_zero_dvd hbdvd) hn.ne'
        · exact hpos
      have hq0 : 0 < n / b := Nat.div_pos (Nat.le_of_dvd hn hbdvd) hb0
      have hqdvd : n / b ∣ n := by
        obtain ⟨c, rfl⟩ := hbdvd
        rw [Nat.mul_div_cancel_left c hb0]
        exact dvd_mul_left c b
      have hmul : b * (n / b) = n := Nat.mul_div_cancel' hbdvd
      -- `√n < b` gives `n < b²`, hence `n/b < b` and `(n/b)² < n`
      have hnlt : n < b * b := Nat.sqrt_lt.mp (by omega)
      have hqlt : n / b < b := Nat.lt_of_mul_lt_mul_left (a := b) (by rw [hmul]; exact hnlt)
      have hqq : (n / b) * (n / b) < n := by
        calc (n / b) * (n / b) < (n / b) * b :=
              Nat.mul_lt_mul_of_pos_left hqlt hq0
          _ = n := by rw [Nat.mul_comm]; exact hmul
      refine ⟨n / b, ?_, nat_div_div_self hbdvd hn⟩
      rw [hA, Finset.mem_filter, hSmall, Finset.mem_filter, Nat.mem_divisors]
      exact ⟨⟨⟨hqdvd, hn.ne'⟩, Nat.le_sqrt.mpr hqq.le⟩, fun h => hqq.ne h⟩
  have hbij : ∑ b ∈ A.image (fun d => n / d), b = ∑ d ∈ A, n / d :=
    Finset.sum_image hinj
  rw [← hbij, himg]

/-- The concrete instance the scanner uses: fuel `100` covers every
`n < 101² = 10201`. -/
theorem sigma100_eq_sigma (n : ℕ) (hn : 0 < n) (hbound : n < 101 * 101) :
    sigma100 n = ∑ d ∈ n.divisors, d :=
  sigmaPair_eq_sigma n 100 hn hbound

/-! ## The scanner -/

/-- The 23 members of `oddAbundantBelow10000`, as a bare list (kernel-fast
membership via `List` recursion, avoiding the `Finset`/`Multiset` quotient). -/
def oddAbundantList : List ℕ :=
  [945, 1575, 2205, 2835, 3465, 4095, 4725, 5355, 5775, 5985, 6435, 6615,
   6825, 7245, 7425, 7875, 8085, 8415, 8505, 8925, 9135, 9555, 9765]

/-- `enumOk X = true` iff every `l ≤ X` that is odd and abundant-or-perfect
(per `sigma100`) lies in `oddAbundantList`. Disjunct order is the cost
order: evens exit after one `% 2`, list members exit after ≤ 23 comparisons,
and only the surviving odd numbers pay the `O(l)` σ computation. -/
def enumOk : ℕ → Bool
  | 0 => true
  | L + 1 =>
    (decide ((L + 1) % 2 = 0)
      || decide ((L + 1) ∈ oddAbundantList)
      || decide (sigma100 (L + 1) < 2 * (L + 1)))
    && enumOk L

/-- List membership transfers to the step-4 `Finset`. -/
theorem mem_oddAbundant_of_mem_list {l : ℕ} (h : l ∈ oddAbundantList) :
    l ∈ oddAbundantBelow10000 := by
  fin_cases h <;> decide

/-- Soundness of the scanner, by induction on the bound. -/
theorem enumOk_sound : ∀ X, enumOk X = true →
    ∀ l, l ≤ X → l % 2 = 1 → 2 * l ≤ sigma100 l → l ∈ oddAbundantBelow10000 := by
  intro X
  induction X with
  | zero =>
    intro _ l hl hodd _
    omega
  | succ X ih =>
    intro h l hl hodd hab
    rw [enumOk, Bool.and_eq_true] at h
    obtain ⟨hhead, htail⟩ := h
    rcases Nat.lt_or_ge l (X + 1) with hlt | hge
    · exact ih htail l (by omega) hodd hab
    · have hleq : l = X + 1 := by omega
      subst hleq
      rw [Bool.or_eq_true, Bool.or_eq_true] at hhead
      rcases hhead with (heven | hlist) | hsig
    -- even: contradicts oddness
      · rw [decide_eq_true_iff] at heven
        omega
      · rw [decide_eq_true_iff] at hlist
        exact mem_oddAbundant_of_mem_list hlist
      · rw [decide_eq_true_iff] at hsig
        omega

/-! ## The kernel computation (the actual enumeration content) -/

set_option maxRecDepth 4000000 in
set_option maxHeartbeats 40000000 in
-- one closed kernel scan of `[0, 10000]`, ≈ 1–2 min of CPU; the default
-- heartbeat budget is sized for ordinary elaboration, not for this
/-- The single closed computation: the scan of `[0, 10000]` passes. Kernel
cost ≈ 1–2 min CPU (the constant-depth `sigma100` makes it linear in the
bound; the naive `Nat.divisors` route was measured infeasible). -/
theorem enum_ok_10000 : enumOk 10000 = true := by
  decide

/-! ## The enumeration lemma -/

/-- **Enumeration.** Every odd `L ≤ 10000` with `2 * L ≤ σ₁ L` is one of the
23 members of `oddAbundantBelow10000`. -/
theorem odd_abundant_le_10000_mem (L : ℕ) (hL : L ≤ 10000) (hodd : L % 2 = 1)
    (hab : 2 * L ≤ ∑ d ∈ L.divisors, d) : L ∈ oddAbundantBelow10000 := by
  have hab' : 2 * L ≤ sigma100 L := by
    rw [sigma100_eq_sigma L (by omega) (by omega)]
    exact hab
  exact enumOk_sound 10000 enum_ok_10000 L hL hodd hab'

/-! ## The composed headline -/

open Finset in
/-- **Headline (steps 1–5).** Any covering of `ℤ` by finitely many congruence
classes with *distinct odd* moduli `> 1` has `lcm > 10000`: the lcm is odd and
abundant-or-perfect (density + oddness, as in `odd_covering_lcm_ge_945`), the
enumeration pins it to one of 23 values, and the step-4 capacity certificates
exclude every one of them. -/
theorem odd_covering_lcm_gt_10000
    {ι : Type} [Fintype ι]
    (n : ι → ℕ) (a : ι → ℤ)
    (hgt : ∀ i, 1 < n i) (hodd : ∀ i, Odd (n i))
    (hinj : Function.Injective n)
    (hcov : ∀ x : ℤ, ∃ i, (n i : ℤ) ∣ (x - a i)) :
    10000 < Finset.univ.lcm n := by
  classical
  by_contra hle
  rw [not_lt] at hle
  set L := Finset.univ.lcm n with hLdef
  have hpos : ∀ i, 0 < n i := fun i => lt_trans Nat.zero_lt_one (hgt i)
  have hdvd : ∀ i, n i ∣ L := fun i => Finset.dvd_lcm (Finset.mem_univ i)
  have hL0 : L ≠ 0 := by
    rw [hLdef, Ne, Finset.lcm_eq_zero_iff]
    rintro ⟨x, -, hx⟩
    exact (hpos x).ne' hx
  -- `L` is abundant-or-perfect: the density bound through the divisor sum.
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
  -- `L` is odd: it divides the odd product of the moduli.
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
  -- Enumeration pins `L`; step 4 excludes it.
  have hmem := odd_abundant_le_10000_mem L hle hLodd habund
  exact covering_lcm_notMem_oddAbundantBelow10000 n a hgt hinj hcov hmem
