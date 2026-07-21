/-
Copyright (c) 2026 Millennium Research. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Millennium Research (Ibby Mian), with Claude
-/
import Erdos7.Density
import Erdos7.AbundancyFloor

/-!
# The capacity bound (Erdős #7, step 4)

The density lemma (`Erdos7.Density`) only charges each congruence class its
raw density `1/d`. This file charges the *CRT-forced overlap* among classes
with pairwise-coprime moduli: if `T` is a pairwise-coprime family of moduli
dividing `N`, the classes over `T` miss at least `(N / ∏ d) * ∏ (d - 1)`
residues in `[0, N)` (exactly the Chinese-Remainder count), and the missed
residues must be covered by the *other* moduli, each of which can only
contribute `N / d` points. For every odd abundant `N ≤ 10000` the resulting
inequality fails, so no covering system has all its moduli among the
divisors `> 1` of such an `N`.

Main results:
* `uncovered_card_ge`      — the CRT counting core: pairwise-coprime classes
                              leave at least `(N / ∏ dᵢ) * ∏ (dᵢ - 1)` points
                              of `[0, N)` uncovered.
* `capacity_exclusion`     — the adversary-free certificate: a per-`N`
                              arithmetic inequality that refutes *every*
                              covering with distinct moduli `> 1` dividing `N`.
* `capacity_exclusion_int` — the ℤ-level form: a covering of `ℤ` with
                              distinct moduli `> 1` cannot have `lcm ∣ N`
                              when `N` carries a capacity certificate.
* `no_covering_lcm_dvd_945` … and 22 further instances: every odd
                              abundant-or-perfect `N < 10000` is excluded.
* `covering_lcm_notMem_oddAbundantBelow10000` — the assembled list form.
* `odd_covering_lcm_gt_945` — strict improvement of the step-1–3 headline:
                              any covering of ℤ by distinct odd moduli `> 1`
                              has `lcm > 945`.

Oddness is *not* needed for the exclusions themselves: the capacity
certificate refutes every covering (odd or not) whose moduli divide the
target `N`. Oddness only enters when composing with the abundancy floor.

The three known stragglers `10395, 12285, 17325` (odd abundant, four prime
factors) are not closed by this bound (see the example at the end of the
file) and are out of scope here.
-/

/-! ## The product of pairwise-coprime divisors divides `N` -/

/-- Pairwise-coprime naturals that each divide `N` have their product divide
`N`. (`Finset.prod_dvd_of_coprime` is unusable here: over `ℕ` the
ring-theoretic `IsCoprime` degenerates.) -/
theorem prod_dvd_of_pairwise_coprime {ι : Type*} {t : Finset ι} {f : ι → ℕ} {N : ℕ}
    (hdvd : ∀ i ∈ t, f i ∣ N)
    (hcop : ∀ i ∈ t, ∀ j ∈ t, i ≠ j → Nat.Coprime (f i) (f j)) :
    ∏ i ∈ t, f i ∣ N := by
  classical
  induction t using Finset.cons_induction with
  | empty => rw [Finset.prod_empty]; exact one_dvd N
  | cons i s his ih =>
    rw [Finset.prod_cons]
    have h1 : f i ∣ N := hdvd i (Finset.mem_cons_self ..)
    have h2 : ∏ j ∈ s, f j ∣ N :=
      ih (fun j hj => hdvd j (Finset.mem_cons_of_mem hj))
        (fun j hj k hk hjk =>
          hcop j (Finset.mem_cons_of_mem hj) k (Finset.mem_cons_of_mem hk) hjk)
    have hcp : Nat.Coprime (f i) (∏ j ∈ s, f j) :=
      Nat.Coprime.prod_right fun j hj =>
        hcop i (Finset.mem_cons_self ..) j (Finset.mem_cons_of_mem hj)
          (by rintro rfl; exact his hj)
    exact hcp.mul_dvd_of_dvd_of_dvd h1 h2

/-! ## The CRT counting core -/

/-- **Uncovered-count lower bound.** Classes `(dᵢ, rᵢ)` with pairwise-coprime
moduli `dᵢ > 1` all dividing `N` leave at least `(N / ∏ dᵢ) * ∏ (dᵢ - 1)`
points of `[0, N)` uncovered: by CRT there are `∏ (dᵢ - 1)` simultaneous
avoiding residues mod `∏ dᵢ`, each recurring `N / ∏ dᵢ` times. -/
theorem uncovered_card_ge {N : ℕ} (U : Finset (ℕ × ℕ))
    (hdvd : ∀ p ∈ U, p.1 ∣ N) (hone : ∀ p ∈ U, 1 < p.1)
    (hcop : ∀ p ∈ U, ∀ q ∈ U, p ≠ q → Nat.Coprime p.1 q.1) :
    (N / ∏ p ∈ U, p.1) * ∏ p ∈ U, (p.1 - 1) ≤
      ((Finset.range N).filter (fun x => ∀ p ∈ U, x % p.1 ≠ p.2)).card := by
  classical
  set P := ∏ p ∈ U, p.1 with hPdef
  have hpos : ∀ p ∈ U, 0 < p.1 := fun p hp => lt_trans one_pos (hone p hp)
  have hs0 : ∀ p ∈ U, p.1 ≠ 0 := fun p hp => (hpos p hp).ne'
  have hPdvd : P ∣ N := prod_dvd_of_pairwise_coprime hdvd hcop
  have hPpos : 0 < P := by
    rw [hPdef]
    exact Nat.pos_of_ne_zero (Finset.prod_ne_zero_iff.mpr hs0)
  have hpair : Set.Pairwise (U : Set (ℕ × ℕ)) (Function.onFun Nat.Coprime Prod.fst) :=
    fun p hp q hq hpq => hcop p hp q hq hpq
  -- The avoiding-residue choices: one non-forbidden residue per modulus.
  set D := U.pi (fun p => (Finset.range p.1).erase (p.2 % p.1)) with hDdef
  -- The CRT witness for a choice `b`, as a total function via a default.
  set crt : (∀ p ∈ U, ℕ) → ℕ := fun b =>
    (Nat.chineseRemainderOfFinset (fun p => if h : p ∈ U then b p h else 0)
      Prod.fst U hs0 hpair : ℕ) with hcrtdef
  have hcrt_lt : ∀ b, crt b < P :=
    fun b => Nat.chineseRemainderOfFinset_lt_prod _ Prod.fst hs0 hpair
  have hcrt_mod : ∀ b ∈ D, ∀ p, ∀ hp : p ∈ U, (crt b) % p.1 = b p hp := by
    intro b hb p hp
    have hmem : b p hp ∈ (Finset.range p.1).erase (p.2 % p.1) :=
      Finset.mem_pi.mp hb p hp
    have hlt : b p hp < p.1 := Finset.mem_range.mp (Finset.mem_of_mem_erase hmem)
    have hmodeq := (Nat.chineseRemainderOfFinset
      (fun q => if h : q ∈ U then b q h else 0) Prod.fst U hs0 hpair).prop p hp
    rw [dif_pos hp] at hmodeq
    calc (crt b) % p.1 = (b p hp) % p.1 := hmodeq
      _ = b p hp := Nat.mod_eq_of_lt hlt
  -- The injection `(choice, block) ↦ crt choice + P * block`.
  have hmaps : ∀ bk ∈ D ×ˢ Finset.range (N / P),
      crt bk.1 + P * bk.2 ∈
        (Finset.range N).filter (fun x => ∀ p ∈ U, x % p.1 ≠ p.2) := by
    rintro ⟨b, k⟩ hbk
    rw [Finset.mem_product] at hbk
    obtain ⟨hb, hk⟩ := hbk
    rw [Finset.mem_range] at hk
    rw [Finset.mem_filter, Finset.mem_range]
    constructor
    · calc crt b + P * k < P + P * k := Nat.add_lt_add_right (hcrt_lt b) _
        _ = P * (k + 1) := by ring
        _ ≤ P * (N / P) := Nat.mul_le_mul_left P (Nat.succ_le_of_lt hk)
        _ = N := Nat.mul_div_cancel' hPdvd
    · intro p hp hbad
      obtain ⟨m, hm⟩ : p.1 ∣ P := Finset.dvd_prod_of_mem _ hp
      have hxmod : (crt b + P * k) % p.1 = (crt b) % p.1 := by
        rw [hm, mul_assoc, Nat.add_mul_mod_self_left]
      rw [hxmod, hcrt_mod b hb p hp] at hbad
      -- `b p hp = p.2` with `b p hp < p.1` forces `b p hp = p.2 % p.1`,
      -- which the erase forbids.
      have hmem : b p hp ∈ (Finset.range p.1).erase (p.2 % p.1) :=
        Finset.mem_pi.mp hb p hp
      have hlt : b p hp < p.1 := Finset.mem_range.mp (Finset.mem_of_mem_erase hmem)
      exact Finset.ne_of_mem_erase hmem (by rw [hbad, Nat.mod_eq_of_lt (hbad ▸ hlt)])
  have hinjmap : Set.InjOn
      (fun bk : ((p : ℕ × ℕ) → p ∈ U → ℕ) × ℕ => crt bk.1 + P * bk.2)
      ↑(D ×ˢ Finset.range (N / P)) := by
    rintro ⟨b, k⟩ hbk ⟨b', k'⟩ hbk' heq
    simp only [Finset.coe_product, Set.mem_prod, Finset.mem_coe] at hbk hbk'
    obtain ⟨hb, -⟩ := hbk
    obtain ⟨hb', -⟩ := hbk'
    simp only at heq
    have hcb : (crt b + P * k) % P = crt b := by
      rw [Nat.add_mul_mod_self_left, Nat.mod_eq_of_lt (hcrt_lt b)]
    have hcb' : (crt b' + P * k') % P = crt b' := by
      rw [Nat.add_mul_mod_self_left, Nat.mod_eq_of_lt (hcrt_lt b')]
    have hc : crt b = crt b' := by rw [← hcb, ← hcb', heq]
    have hk : k = k' := by
      have h1 : P * k = P * k' := by omega
      exact Nat.eq_of_mul_eq_mul_left hPpos h1
    have hbfun : b = b' := by
      funext p hp
      rw [← hcrt_mod b hb p hp, ← hcrt_mod b' hb' p hp, hc]
    exact Prod.ext hbfun hk
  have hDcard : D.card = ∏ p ∈ U, (p.1 - 1) := by
    rw [hDdef, Finset.card_pi]
    exact Finset.prod_congr rfl fun p hp => by
      rw [Finset.card_erase_of_mem (Finset.mem_range.mpr (Nat.mod_lt _ (hpos p hp))),
        Finset.card_range]
  have hdomcard : (D ×ˢ Finset.range (N / P)).card = N / P * ∏ p ∈ U, (p.1 - 1) := by
    rw [Finset.card_product, hDcard, Finset.card_range, mul_comm]
  calc N / P * ∏ p ∈ U, (p.1 - 1)
      = (D ×ˢ Finset.range (N / P)).card := hdomcard.symm
    _ ≤ ((Finset.range N).filter (fun x => ∀ p ∈ U, x % p.1 ≠ p.2)).card :=
        Finset.card_le_card_of_injOn _ hmaps hinjmap

/-! ## Monotone relaxation: shrinking the coprime family weakens the bound -/

/-- Dropping members from a pairwise-coprime divisor family only lowers the
capacity product, so a certificate stated over the *full* family `T` applies
to whatever subfamily a covering actually uses. -/
theorem capacity_prod_relax {N : ℕ} {V T : Finset ℕ} (hVT : V ⊆ T)
    (hTdvd : ∀ d ∈ T, d ∣ N) (hTone : ∀ d ∈ T, 1 < d)
    (hTcop : ∀ d ∈ T, ∀ e ∈ T, d ≠ e → Nat.Coprime d e) :
    (N / ∏ d ∈ T, d) * ∏ d ∈ T, (d - 1) ≤
      (N / ∏ d ∈ V, d) * ∏ d ∈ V, (d - 1) := by
  classical
  have hs0 : ∀ d ∈ T, d ≠ 0 := fun d hd => (lt_trans one_pos (hTone d hd)).ne'
  have hPT : ∏ d ∈ T, d ∣ N :=
    prod_dvd_of_pairwise_coprime hTdvd hTcop
  have hsplit : (∏ d ∈ T \ V, d) * ∏ d ∈ V, d = ∏ d ∈ T, d :=
    Finset.prod_sdiff hVT
  have hPVpos : 0 < ∏ d ∈ V, d :=
    Nat.pos_of_ne_zero (Finset.prod_ne_zero_iff.mpr fun d hd => hs0 d (hVT hd))
  obtain ⟨m, hm⟩ := hPT
  have hPTpos : 0 < ∏ d ∈ T, d :=
    Nat.pos_of_ne_zero (Finset.prod_ne_zero_iff.mpr hs0)
  have hNT : N / ∏ d ∈ T, d = m := by rw [hm, Nat.mul_div_cancel_left _ hPTpos]
  have hNV : N / ∏ d ∈ V, d = (∏ d ∈ T \ V, d) * m := by
    rw [hm, ← hsplit, mul_comm (∏ d ∈ T \ V, d) (∏ d ∈ V, d), mul_assoc,
      Nat.mul_div_cancel_left _ hPVpos]
  have hprodsplit : (∏ d ∈ T \ V, (d - 1)) * ∏ d ∈ V, (d - 1) = ∏ d ∈ T, (d - 1) :=
    Finset.prod_sdiff hVT
  have hQle : ∏ d ∈ T \ V, (d - 1) ≤ ∏ d ∈ T \ V, d :=
    Finset.prod_le_prod' fun d _ => Nat.sub_le d 1
  calc (N / ∏ d ∈ T, d) * ∏ d ∈ T, (d - 1)
      = (∏ d ∈ T \ V, (d - 1)) * (m * ∏ d ∈ V, (d - 1)) := by
        rw [hNT, ← hprodsplit]; ring
    _ ≤ (∏ d ∈ T \ V, d) * (m * ∏ d ∈ V, (d - 1)) :=
        Nat.mul_le_mul_right _ hQle
    _ = (N / ∏ d ∈ V, d) * ∏ d ∈ V, (d - 1) := by rw [hNV]; ring

/-! ## The capacity certificate -/

/-- **Capacity exclusion.** Fix `N` and a pairwise-coprime family `T` of
divisors `> 1` of `N`. If the arithmetic inequality

`∑_{d ∣ N, d > 1, d ∉ T} N / d  <  (N / ∏ T) * ∏_{d ∈ T} (d - 1)`

holds, then **no** system of congruence classes with distinct moduli `> 1`
all dividing `N` covers `[0, N)`. The left side is everything the non-`T`
moduli can cover of the CRT-guaranteed uncovered set; the right side is that
set's size. The hypothesis is decidable, so instances discharge by `decide`. -/
theorem capacity_exclusion {N : ℕ} (hN : 0 < N) (T : Finset ℕ)
    (hTdvd : ∀ d ∈ T, d ∣ N) (hTone : ∀ d ∈ T, 1 < d)
    (hTcop : ∀ d ∈ T, ∀ e ∈ T, d ≠ e → Nat.Coprime d e)
    (harith : ∑ d ∈ (N.divisors.erase 1) \ T, N / d <
      (N / ∏ d ∈ T, d) * ∏ d ∈ T, (d - 1))
    (S : Finset (ℕ × ℕ))
    (hdvd : ∀ p ∈ S, p.1 ∣ N) (hone : ∀ p ∈ S, 1 < p.1)
    (hinj : Set.InjOn Prod.fst (S : Set (ℕ × ℕ)))
    (hcov : ∀ x < N, ∃ p ∈ S, x % p.1 = p.2) : False := by
  classical
  set U := S.filter (fun p => p.1 ∈ T) with hUdef
  set W := S.filter (fun p => p.1 ∉ T) with hWdef
  have hUsub : U ⊆ S := Finset.filter_subset _ _
  have hWsub : W ⊆ S := Finset.filter_subset _ _
  have hUcop : ∀ p ∈ U, ∀ q ∈ U, p ≠ q → Nat.Coprime p.1 q.1 := by
    intro p hp q hq hpq
    have hpS := hUsub hp
    have hqS := hUsub hq
    have hpT : p.1 ∈ T := (Finset.mem_filter.mp hp).2
    have hqT : q.1 ∈ T := (Finset.mem_filter.mp hq).2
    by_cases hfst : p.1 = q.1
    · exact absurd (hinj (Finset.mem_coe.mpr hpS) (Finset.mem_coe.mpr hqS) hfst) hpq
    · exact hTcop p.1 hpT q.1 hqT hfst
  -- CRT floor for the classes over `T` actually used.
  have hfloor := uncovered_card_ge U (fun p hp => hdvd p (hUsub hp))
    (fun p hp => hone p (hUsub hp)) hUcop
  -- Every point the `U`-classes miss is covered by a `W`-class.
  set A := (Finset.range N).filter (fun x => ∀ p ∈ U, x % p.1 ≠ p.2) with hAdef
  have hAsub : A ⊆ W.biUnion
      (fun p => (Finset.range N).filter (fun x => x % p.1 = p.2)) := by
    intro x hx
    rw [hAdef, Finset.mem_filter, Finset.mem_range] at hx
    obtain ⟨hxN, havoid⟩ := hx
    obtain ⟨p, hpS, hp⟩ := hcov x hxN
    have hpW : p ∈ W := by
      rw [hWdef, Finset.mem_filter]
      refine ⟨hpS, fun hpT => ?_⟩
      exact havoid p (Finset.mem_filter.mpr ⟨hpS, hpT⟩) hp
    exact Finset.mem_biUnion.mpr
      ⟨p, hpW, Finset.mem_filter.mpr ⟨Finset.mem_range.mpr hxN, hp⟩⟩
  have hAcard : A.card ≤ ∑ p ∈ W, N / p.1 :=
    calc A.card
        ≤ (W.biUnion (fun p => (Finset.range N).filter (fun x => x % p.1 = p.2))).card :=
          Finset.card_le_card hAsub
      _ ≤ ∑ p ∈ W, ((Finset.range N).filter (fun x => x % p.1 = p.2)).card :=
          Finset.card_biUnion_le
      _ ≤ ∑ p ∈ W, N / p.1 :=
          Finset.sum_le_sum fun p hp => card_filter_mod_le N p.1 p.2 (hdvd p (hWsub hp))
  -- The `W`-moduli are distinct divisors `> 1` of `N` outside `T`.
  have hWinj : ∀ x ∈ W, ∀ y ∈ W, x.1 = y.1 → x = y := fun x hx y hy h =>
    hinj (Finset.mem_coe.mpr (hWsub hx)) (Finset.mem_coe.mpr (hWsub hy)) h
  have hWimg : ∑ d ∈ W.image Prod.fst, N / d = ∑ p ∈ W, N / p.1 :=
    Finset.sum_image hWinj
  have hWsubdiv : W.image Prod.fst ⊆ (N.divisors.erase 1) \ T := by
    intro d hd
    obtain ⟨p, hpW, rfl⟩ := Finset.mem_image.mp hd
    rw [Finset.mem_sdiff, Finset.mem_erase, Nat.mem_divisors]
    exact ⟨⟨(hone p (hWsub hpW)).ne', hdvd p (hWsub hpW), hN.ne'⟩,
      (Finset.mem_filter.mp hpW).2⟩
  have hWbound : ∑ p ∈ W, N / p.1 ≤ ∑ d ∈ (N.divisors.erase 1) \ T, N / d := by
    rw [← hWimg]
    exact Finset.sum_le_sum_of_subset hWsubdiv
  -- The used `T`-moduli form a subfamily of `T`; relax the floor to full `T`.
  have hUinj : ∀ x ∈ U, ∀ y ∈ U, x.1 = y.1 → x = y := fun x hx y hy h =>
    hinj (Finset.mem_coe.mpr (hUsub hx)) (Finset.mem_coe.mpr (hUsub hy)) h
  have hVT : U.image Prod.fst ⊆ T := by
    intro d hd
    obtain ⟨p, hpU, rfl⟩ := Finset.mem_image.mp hd
    exact (Finset.mem_filter.mp hpU).2
  have hprodV : ∏ d ∈ U.image Prod.fst, d = ∏ p ∈ U, p.1 :=
    Finset.prod_image hUinj
  have hprodV1 : ∏ d ∈ U.image Prod.fst, (d - 1) = ∏ p ∈ U, (p.1 - 1) :=
    Finset.prod_image hUinj
  have hrelax := capacity_prod_relax hVT hTdvd hTone hTcop
  rw [hprodV, hprodV1] at hrelax
  -- Chain everything; contradict the certificate.
  have hchain : (N / ∏ d ∈ T, d) * ∏ d ∈ T, (d - 1) ≤
      ∑ d ∈ (N.divisors.erase 1) \ T, N / d :=
    le_trans hrelax (le_trans hfloor (le_trans hAcard hWbound))
  exact absurd hchain (not_le.mpr harith)

/-! ## ℤ-level form -/

open Finset in
/-- **ℤ-level capacity exclusion.** A covering of `ℤ` by congruence classes
with *distinct* moduli `> 1` cannot have its lcm divide any `N` carrying a
capacity certificate. Oddness is not required. -/
theorem capacity_exclusion_int
    {ι : Type} [Fintype ι] (n : ι → ℕ) (a : ι → ℤ)
    (hgt : ∀ i, 1 < n i) (hinj : Function.Injective n)
    (hcov : ∀ x : ℤ, ∃ i, (n i : ℤ) ∣ (x - a i))
    {N : ℕ} (hN : 0 < N) (hlcm : Finset.univ.lcm n ∣ N)
    (T : Finset ℕ)
    (hTdvd : ∀ d ∈ T, d ∣ N) (hTone : ∀ d ∈ T, 1 < d)
    (hTcop : ∀ d ∈ T, ∀ e ∈ T, d ≠ e → Nat.Coprime d e)
    (harith : ∑ d ∈ (N.divisors.erase 1) \ T, N / d <
      (N / ∏ d ∈ T, d) * ∏ d ∈ T, (d - 1)) : False := by
  classical
  have hdvdN : ∀ i, n i ∣ N :=
    fun i => dvd_trans (Finset.dvd_lcm (Finset.mem_univ i)) hlcm
  set r : ι → ℕ := fun i => ((a i) % (n i : ℤ)).toNat with hrdef
  set S : Finset (ℕ × ℕ) := Finset.univ.image (fun i => (n i, r i)) with hSdef
  have hdvd : ∀ p ∈ S, p.1 ∣ N := by
    intro p hp
    obtain ⟨i, -, rfl⟩ := Finset.mem_image.mp hp
    exact hdvdN i
  have hone : ∀ p ∈ S, 1 < p.1 := by
    intro p hp
    obtain ⟨i, -, rfl⟩ := Finset.mem_image.mp hp
    exact hgt i
  have hinjS : Set.InjOn Prod.fst (S : Set (ℕ × ℕ)) := by
    intro p hp q hq hfst
    rw [Finset.mem_coe, hSdef, Finset.mem_image] at hp hq
    obtain ⟨i, -, rfl⟩ := hp
    obtain ⟨j, -, rfl⟩ := hq
    have : i = j := hinj hfst
    rw [this]
  have hcov' : ∀ x < N, ∃ p ∈ S, x % p.1 = p.2 := by
    intro x _
    obtain ⟨i, hi⟩ := hcov (x : ℤ)
    refine ⟨(n i, r i), Finset.mem_image.2 ⟨i, Finset.mem_univ i, rfl⟩, ?_⟩
    have h1 : (a i) % (n i : ℤ) = (x : ℤ) % (n i : ℤ) := Int.modEq_iff_dvd.mpr hi
    have h2 : ((x : ℤ)) % (n i : ℤ) = ((x % n i : ℕ) : ℤ) := by
      rw [Int.natCast_mod]
    show x % n i = r i
    rw [hrdef]
    simp only [h1, h2, Int.toNat_natCast]
  exact capacity_exclusion hN T hTdvd hTone hTcop harith S hdvd hone hinjS hcov'

section instances
set_option maxRecDepth 600000

/-! ## The 23 instances: every odd abundant-or-perfect `N < 10000` is excluded -/

theorem no_covering_lcm_dvd_945
    {ι : Type} [Fintype ι] (n : ι → ℕ) (a : ι → ℤ)
    (hgt : ∀ i, 1 < n i) (hinj : Function.Injective n)
    (hcov : ∀ x : ℤ, ∃ i, (n i : ℤ) ∣ (x - a i)) :
    ¬ Finset.univ.lcm n ∣ 945 := fun hdvd =>
  capacity_exclusion_int n a hgt hinj hcov (by norm_num) hdvd
    ({3, 5, 7} : Finset ℕ) (by decide) (by decide) (by decide) (by decide)

theorem no_covering_lcm_dvd_1575
    {ι : Type} [Fintype ι] (n : ι → ℕ) (a : ι → ℤ)
    (hgt : ∀ i, 1 < n i) (hinj : Function.Injective n)
    (hcov : ∀ x : ℤ, ∃ i, (n i : ℤ) ∣ (x - a i)) :
    ¬ Finset.univ.lcm n ∣ 1575 := fun hdvd =>
  capacity_exclusion_int n a hgt hinj hcov (by norm_num) hdvd
    ({3, 5, 7} : Finset ℕ) (by decide) (by decide) (by decide) (by decide)

theorem no_covering_lcm_dvd_2205
    {ι : Type} [Fintype ι] (n : ι → ℕ) (a : ι → ℤ)
    (hgt : ∀ i, 1 < n i) (hinj : Function.Injective n)
    (hcov : ∀ x : ℤ, ∃ i, (n i : ℤ) ∣ (x - a i)) :
    ¬ Finset.univ.lcm n ∣ 2205 := fun hdvd =>
  capacity_exclusion_int n a hgt hinj hcov (by norm_num) hdvd
    ({3, 5, 7} : Finset ℕ) (by decide) (by decide) (by decide) (by decide)

theorem no_covering_lcm_dvd_2835
    {ι : Type} [Fintype ι] (n : ι → ℕ) (a : ι → ℤ)
    (hgt : ∀ i, 1 < n i) (hinj : Function.Injective n)
    (hcov : ∀ x : ℤ, ∃ i, (n i : ℤ) ∣ (x - a i)) :
    ¬ Finset.univ.lcm n ∣ 2835 := fun hdvd =>
  capacity_exclusion_int n a hgt hinj hcov (by norm_num) hdvd
    ({3, 5, 7} : Finset ℕ) (by decide) (by decide) (by decide) (by decide)

theorem no_covering_lcm_dvd_3465
    {ι : Type} [Fintype ι] (n : ι → ℕ) (a : ι → ℤ)
    (hgt : ∀ i, 1 < n i) (hinj : Function.Injective n)
    (hcov : ∀ x : ℤ, ∃ i, (n i : ℤ) ∣ (x - a i)) :
    ¬ Finset.univ.lcm n ∣ 3465 := fun hdvd =>
  capacity_exclusion_int n a hgt hinj hcov (by norm_num) hdvd
    ({3, 5, 7, 11} : Finset ℕ) (by decide) (by decide) (by decide) (by decide)

theorem no_covering_lcm_dvd_4095
    {ι : Type} [Fintype ι] (n : ι → ℕ) (a : ι → ℤ)
    (hgt : ∀ i, 1 < n i) (hinj : Function.Injective n)
    (hcov : ∀ x : ℤ, ∃ i, (n i : ℤ) ∣ (x - a i)) :
    ¬ Finset.univ.lcm n ∣ 4095 := fun hdvd =>
  capacity_exclusion_int n a hgt hinj hcov (by norm_num) hdvd
    ({3, 5, 7, 13} : Finset ℕ) (by decide) (by decide) (by decide) (by decide)

theorem no_covering_lcm_dvd_4725
    {ι : Type} [Fintype ι] (n : ι → ℕ) (a : ι → ℤ)
    (hgt : ∀ i, 1 < n i) (hinj : Function.Injective n)
    (hcov : ∀ x : ℤ, ∃ i, (n i : ℤ) ∣ (x - a i)) :
    ¬ Finset.univ.lcm n ∣ 4725 := fun hdvd =>
  capacity_exclusion_int n a hgt hinj hcov (by norm_num) hdvd
    ({3, 5, 7} : Finset ℕ) (by decide) (by decide) (by decide) (by decide)

theorem no_covering_lcm_dvd_5355
    {ι : Type} [Fintype ι] (n : ι → ℕ) (a : ι → ℤ)
    (hgt : ∀ i, 1 < n i) (hinj : Function.Injective n)
    (hcov : ∀ x : ℤ, ∃ i, (n i : ℤ) ∣ (x - a i)) :
    ¬ Finset.univ.lcm n ∣ 5355 := fun hdvd =>
  capacity_exclusion_int n a hgt hinj hcov (by norm_num) hdvd
    ({3, 5, 7, 17} : Finset ℕ) (by decide) (by decide) (by decide) (by decide)

theorem no_covering_lcm_dvd_5775
    {ι : Type} [Fintype ι] (n : ι → ℕ) (a : ι → ℤ)
    (hgt : ∀ i, 1 < n i) (hinj : Function.Injective n)
    (hcov : ∀ x : ℤ, ∃ i, (n i : ℤ) ∣ (x - a i)) :
    ¬ Finset.univ.lcm n ∣ 5775 := fun hdvd =>
  capacity_exclusion_int n a hgt hinj hcov (by norm_num) hdvd
    ({3, 5, 7, 11} : Finset ℕ) (by decide) (by decide) (by decide) (by decide)

theorem no_covering_lcm_dvd_5985
    {ι : Type} [Fintype ι] (n : ι → ℕ) (a : ι → ℤ)
    (hgt : ∀ i, 1 < n i) (hinj : Function.Injective n)
    (hcov : ∀ x : ℤ, ∃ i, (n i : ℤ) ∣ (x - a i)) :
    ¬ Finset.univ.lcm n ∣ 5985 := fun hdvd =>
  capacity_exclusion_int n a hgt hinj hcov (by norm_num) hdvd
    ({3, 5, 7, 19} : Finset ℕ) (by decide) (by decide) (by decide) (by decide)

theorem no_covering_lcm_dvd_6435
    {ι : Type} [Fintype ι] (n : ι → ℕ) (a : ι → ℤ)
    (hgt : ∀ i, 1 < n i) (hinj : Function.Injective n)
    (hcov : ∀ x : ℤ, ∃ i, (n i : ℤ) ∣ (x - a i)) :
    ¬ Finset.univ.lcm n ∣ 6435 := fun hdvd =>
  capacity_exclusion_int n a hgt hinj hcov (by norm_num) hdvd
    ({3, 5, 11, 13} : Finset ℕ) (by decide) (by decide) (by decide) (by decide)

theorem no_covering_lcm_dvd_6615
    {ι : Type} [Fintype ι] (n : ι → ℕ) (a : ι → ℤ)
    (hgt : ∀ i, 1 < n i) (hinj : Function.Injective n)
    (hcov : ∀ x : ℤ, ∃ i, (n i : ℤ) ∣ (x - a i)) :
    ¬ Finset.univ.lcm n ∣ 6615 := fun hdvd =>
  capacity_exclusion_int n a hgt hinj hcov (by norm_num) hdvd
    ({3, 5, 7} : Finset ℕ) (by decide) (by decide) (by decide) (by decide)

theorem no_covering_lcm_dvd_6825
    {ι : Type} [Fintype ι] (n : ι → ℕ) (a : ι → ℤ)
    (hgt : ∀ i, 1 < n i) (hinj : Function.Injective n)
    (hcov : ∀ x : ℤ, ∃ i, (n i : ℤ) ∣ (x - a i)) :
    ¬ Finset.univ.lcm n ∣ 6825 := fun hdvd =>
  capacity_exclusion_int n a hgt hinj hcov (by norm_num) hdvd
    ({3, 5, 7, 13} : Finset ℕ) (by decide) (by decide) (by decide) (by decide)

theorem no_covering_lcm_dvd_7245
    {ι : Type} [Fintype ι] (n : ι → ℕ) (a : ι → ℤ)
    (hgt : ∀ i, 1 < n i) (hinj : Function.Injective n)
    (hcov : ∀ x : ℤ, ∃ i, (n i : ℤ) ∣ (x - a i)) :
    ¬ Finset.univ.lcm n ∣ 7245 := fun hdvd =>
  capacity_exclusion_int n a hgt hinj hcov (by norm_num) hdvd
    ({3, 5, 7, 23} : Finset ℕ) (by decide) (by decide) (by decide) (by decide)

theorem no_covering_lcm_dvd_7425
    {ι : Type} [Fintype ι] (n : ι → ℕ) (a : ι → ℤ)
    (hgt : ∀ i, 1 < n i) (hinj : Function.Injective n)
    (hcov : ∀ x : ℤ, ∃ i, (n i : ℤ) ∣ (x - a i)) :
    ¬ Finset.univ.lcm n ∣ 7425 := fun hdvd =>
  capacity_exclusion_int n a hgt hinj hcov (by norm_num) hdvd
    ({3, 5, 11} : Finset ℕ) (by decide) (by decide) (by decide) (by decide)

theorem no_covering_lcm_dvd_7875
    {ι : Type} [Fintype ι] (n : ι → ℕ) (a : ι → ℤ)
    (hgt : ∀ i, 1 < n i) (hinj : Function.Injective n)
    (hcov : ∀ x : ℤ, ∃ i, (n i : ℤ) ∣ (x - a i)) :
    ¬ Finset.univ.lcm n ∣ 7875 := fun hdvd =>
  capacity_exclusion_int n a hgt hinj hcov (by norm_num) hdvd
    ({3, 5, 7} : Finset ℕ) (by decide) (by decide) (by decide) (by decide)

theorem no_covering_lcm_dvd_8085
    {ι : Type} [Fintype ι] (n : ι → ℕ) (a : ι → ℤ)
    (hgt : ∀ i, 1 < n i) (hinj : Function.Injective n)
    (hcov : ∀ x : ℤ, ∃ i, (n i : ℤ) ∣ (x - a i)) :
    ¬ Finset.univ.lcm n ∣ 8085 := fun hdvd =>
  capacity_exclusion_int n a hgt hinj hcov (by norm_num) hdvd
    ({3, 5, 7, 11} : Finset ℕ) (by decide) (by decide) (by decide) (by decide)

theorem no_covering_lcm_dvd_8415
    {ι : Type} [Fintype ι] (n : ι → ℕ) (a : ι → ℤ)
    (hgt : ∀ i, 1 < n i) (hinj : Function.Injective n)
    (hcov : ∀ x : ℤ, ∃ i, (n i : ℤ) ∣ (x - a i)) :
    ¬ Finset.univ.lcm n ∣ 8415 := fun hdvd =>
  capacity_exclusion_int n a hgt hinj hcov (by norm_num) hdvd
    ({3, 5, 11, 17} : Finset ℕ) (by decide) (by decide) (by decide) (by decide)

theorem no_covering_lcm_dvd_8505
    {ι : Type} [Fintype ι] (n : ι → ℕ) (a : ι → ℤ)
    (hgt : ∀ i, 1 < n i) (hinj : Function.Injective n)
    (hcov : ∀ x : ℤ, ∃ i, (n i : ℤ) ∣ (x - a i)) :
    ¬ Finset.univ.lcm n ∣ 8505 := fun hdvd =>
  capacity_exclusion_int n a hgt hinj hcov (by norm_num) hdvd
    ({3, 5, 7} : Finset ℕ) (by decide) (by decide) (by decide) (by decide)

theorem no_covering_lcm_dvd_8925
    {ι : Type} [Fintype ι] (n : ι → ℕ) (a : ι → ℤ)
    (hgt : ∀ i, 1 < n i) (hinj : Function.Injective n)
    (hcov : ∀ x : ℤ, ∃ i, (n i : ℤ) ∣ (x - a i)) :
    ¬ Finset.univ.lcm n ∣ 8925 := fun hdvd =>
  capacity_exclusion_int n a hgt hinj hcov (by norm_num) hdvd
    ({3, 5, 7, 17} : Finset ℕ) (by decide) (by decide) (by decide) (by decide)

theorem no_covering_lcm_dvd_9135
    {ι : Type} [Fintype ι] (n : ι → ℕ) (a : ι → ℤ)
    (hgt : ∀ i, 1 < n i) (hinj : Function.Injective n)
    (hcov : ∀ x : ℤ, ∃ i, (n i : ℤ) ∣ (x - a i)) :
    ¬ Finset.univ.lcm n ∣ 9135 := fun hdvd =>
  capacity_exclusion_int n a hgt hinj hcov (by norm_num) hdvd
    ({3, 5, 7, 29} : Finset ℕ) (by decide) (by decide) (by decide) (by decide)

theorem no_covering_lcm_dvd_9555
    {ι : Type} [Fintype ι] (n : ι → ℕ) (a : ι → ℤ)
    (hgt : ∀ i, 1 < n i) (hinj : Function.Injective n)
    (hcov : ∀ x : ℤ, ∃ i, (n i : ℤ) ∣ (x - a i)) :
    ¬ Finset.univ.lcm n ∣ 9555 := fun hdvd =>
  capacity_exclusion_int n a hgt hinj hcov (by norm_num) hdvd
    ({3, 5, 7, 13} : Finset ℕ) (by decide) (by decide) (by decide) (by decide)

theorem no_covering_lcm_dvd_9765
    {ι : Type} [Fintype ι] (n : ι → ℕ) (a : ι → ℤ)
    (hgt : ∀ i, 1 < n i) (hinj : Function.Injective n)
    (hcov : ∀ x : ℤ, ∃ i, (n i : ℤ) ∣ (x - a i)) :
    ¬ Finset.univ.lcm n ∣ 9765 := fun hdvd =>
  capacity_exclusion_int n a hgt hinj hcov (by norm_num) hdvd
    ({3, 5, 7, 31} : Finset ℕ) (by decide) (by decide) (by decide) (by decide)

/-- The odd abundant-or-perfect numbers below `10000` (there are 23; none is
perfect). The list itself is established by exhaustive search *outside* Lean;
this file only asserts exclusions for its members. Its completeness — that no
other odd `N < 10000` has `2 * N ≤ σ₁ N` — is the step-5 enumeration lemma
and is not claimed here. -/
def oddAbundantBelow10000 : Finset ℕ :=
  {945, 1575, 2205, 2835, 3465, 4095, 4725, 5355, 5775, 5985, 6435, 6615, 6825, 7245, 7425, 7875, 8085, 8415, 8505, 8925, 9135, 9555, 9765}

theorem covering_lcm_notMem_oddAbundantBelow10000
    {ι : Type} [Fintype ι] (n : ι → ℕ) (a : ι → ℤ)
    (hgt : ∀ i, 1 < n i) (hinj : Function.Injective n)
    (hcov : ∀ x : ℤ, ∃ i, (n i : ℤ) ∣ (x - a i)) :
    Finset.univ.lcm n ∉ oddAbundantBelow10000 := by
  intro hmem
  simp only [oddAbundantBelow10000, Finset.mem_insert, Finset.mem_singleton] at hmem
  rcases hmem with h|h|h|h|h|h|h|h|h|h|h|h|h|h|h|h|h|h|h|h|h|h|h
  · exact no_covering_lcm_dvd_945 n a hgt hinj hcov (dvd_of_eq h)
  · exact no_covering_lcm_dvd_1575 n a hgt hinj hcov (dvd_of_eq h)
  · exact no_covering_lcm_dvd_2205 n a hgt hinj hcov (dvd_of_eq h)
  · exact no_covering_lcm_dvd_2835 n a hgt hinj hcov (dvd_of_eq h)
  · exact no_covering_lcm_dvd_3465 n a hgt hinj hcov (dvd_of_eq h)
  · exact no_covering_lcm_dvd_4095 n a hgt hinj hcov (dvd_of_eq h)
  · exact no_covering_lcm_dvd_4725 n a hgt hinj hcov (dvd_of_eq h)
  · exact no_covering_lcm_dvd_5355 n a hgt hinj hcov (dvd_of_eq h)
  · exact no_covering_lcm_dvd_5775 n a hgt hinj hcov (dvd_of_eq h)
  · exact no_covering_lcm_dvd_5985 n a hgt hinj hcov (dvd_of_eq h)
  · exact no_covering_lcm_dvd_6435 n a hgt hinj hcov (dvd_of_eq h)
  · exact no_covering_lcm_dvd_6615 n a hgt hinj hcov (dvd_of_eq h)
  · exact no_covering_lcm_dvd_6825 n a hgt hinj hcov (dvd_of_eq h)
  · exact no_covering_lcm_dvd_7245 n a hgt hinj hcov (dvd_of_eq h)
  · exact no_covering_lcm_dvd_7425 n a hgt hinj hcov (dvd_of_eq h)
  · exact no_covering_lcm_dvd_7875 n a hgt hinj hcov (dvd_of_eq h)
  · exact no_covering_lcm_dvd_8085 n a hgt hinj hcov (dvd_of_eq h)
  · exact no_covering_lcm_dvd_8415 n a hgt hinj hcov (dvd_of_eq h)
  · exact no_covering_lcm_dvd_8505 n a hgt hinj hcov (dvd_of_eq h)
  · exact no_covering_lcm_dvd_8925 n a hgt hinj hcov (dvd_of_eq h)
  · exact no_covering_lcm_dvd_9135 n a hgt hinj hcov (dvd_of_eq h)
  · exact no_covering_lcm_dvd_9555 n a hgt hinj hcov (dvd_of_eq h)
  · exact no_covering_lcm_dvd_9765 n a hgt hinj hcov (dvd_of_eq h)

/-! ## Controls -/

/-- Positive control (soundness): the certificate arithmetic must NOT hold at
`N = 12`, which hosts the classic covering
`{0 mod 2, 0 mod 3, 1 mod 4, 5 mod 6, 7 mod 12}` — checked here for both
maximal pairwise-coprime families. A certificate firing at `12` would mean
the bound is unsound. -/
example : ¬ (∑ d ∈ ((12:ℕ).divisors.erase 1) \ {3, 4}, 12 / d <
    (12 / ∏ d ∈ ({3, 4} : Finset ℕ), d) * ∏ d ∈ ({3, 4} : Finset ℕ), (d - 1)) := by
  decide

example : ¬ (∑ d ∈ ((12:ℕ).divisors.erase 1) \ {2, 3}, 12 / d <
    (12 / ∏ d ∈ ({2, 3} : Finset ℕ), d) * ∏ d ∈ ({2, 3} : Finset ℕ), (d - 1)) := by
  decide

/-- Limit of the method: the first straggler `10395 = 3³·5·7·11` is not
closed by the capacity bound; its certificate hypothesis is false at the prime family
(and, having only four distinct primes, it offers no better family). The
stragglers `10395, 12285, 17325` remain open in this development. -/
example : ¬ (∑ d ∈ ((10395:ℕ).divisors.erase 1) \ {3, 5, 7, 11}, 10395 / d <
    (10395 / ∏ d ∈ ({3, 5, 7, 11} : Finset ℕ), d) *
      ∏ d ∈ ({3, 5, 7, 11} : Finset ℕ), (d - 1)) := by
  decide

end instances

/-! ## Improved headline -/

/-- **Improved headline (steps 1–4).** Any covering of `ℤ` by finitely many
congruence classes with *distinct odd* moduli `> 1` has `lcm > 945`: the
abundancy floor (`odd_covering_lcm_ge_945`) gives `≥ 945`, and the capacity
certificate at `945` refutes equality. -/
theorem odd_covering_lcm_gt_945
    {ι : Type} [Fintype ι] (n : ι → ℕ) (a : ι → ℤ)
    (hgt : ∀ i, 1 < n i) (hodd : ∀ i, Odd (n i))
    (hinj : Function.Injective n)
    (hcov : ∀ x : ℤ, ∃ i, (n i : ℤ) ∣ (x - a i)) :
    945 < Finset.univ.lcm n := by
  rcases lt_or_eq_of_le (odd_covering_lcm_ge_945 n a hgt hodd hinj hcov) with h | h
  · exact h
  · exact absurd (dvd_of_eq h.symm) (no_covering_lcm_dvd_945 n a hgt hinj hcov)
