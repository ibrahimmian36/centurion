/-
Copyright (c) 2026 Millennium Research. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Millennium Research (Ibby Mian), with Claude
-/
import Erdos7.Enumeration

/-!
# The periodicity bridge for Erdős problem 7 (odd covering systems)

A finite family of congruence classes `x ≡ r i [ZMOD d i]`, with every modulus `d i`
dividing a common multiple `N`, covers **all of `ℤ`** if and only if the images of those
classes cover the **finite** ring `ZMod N`.

This is the lemma that lets a finite `ZMod N` / SAT computation say something about `ℤ`.
Both directions are proved with no `sorry`:

* `Erdos7.coversInt_of_coversZMod` — positive finite witness ⟹ covering of `ℤ`.
* `Erdos7.coversZMod_of_coversInt` — covering of `ℤ` ⟹ the finite check succeeds.
  This is the direction that powers **exclusion**: its contrapositive
  (`Erdos7.not_coversInt_of_not_coversZMod`, `Erdos7.forall_not_coversInt`) turns a finite
  UNSAT result into "no covering of `ℤ` exists with these moduli".
-/

namespace Erdos7

section Bridge

variable {ι : Type*} {N : ℕ} {d : ι → ℕ} {r : ι → ℤ}

/-- `x` lies in the congruence class with modulus `d i` and residue `r i`,
spelled as divisibility. Nothing here is finite: `ι` is an arbitrary type. -/
def InClass (d : ι → ℕ) (r : ι → ℤ) (i : ι) (x : ℤ) : Prop := (d i : ℤ) ∣ (x - r i)

/-- The family of congruence classes covers every integer. -/
def CoversInt (d : ι → ℕ) (r : ι → ℤ) : Prop := ∀ x : ℤ, ∃ i, InClass d r i x

/-- The images of the classes cover `ZMod N`, where every modulus divides `N`.
Class `i` is tested by reducing along the ring hom `ZMod N →+* ZMod (d i)`. -/
def CoversZMod (N : ℕ) (d : ι → ℕ) (r : ι → ℤ) (hdvd : ∀ i, d i ∣ N) : Prop :=
  ∀ y : ZMod N, ∃ i, ZMod.castHom (hdvd i) (ZMod (d i)) y = ((r i : ℤ) : ZMod (d i))

/-- Membership in a class, transported into `ZMod (d i)`. -/
theorem inClass_iff_intCast_eq (i : ι) (x : ℤ) :
    InClass d r i x ↔ ((x : ℤ) : ZMod (d i)) = ((r i : ℤ) : ZMod (d i)) := by
  rw [InClass, eq_comm, ZMod.intCast_eq_intCast_iff_dvd_sub]

/-- The reduction map `ZMod N →+* ZMod (d i)` commutes with `Int.cast`.
This is the only place the hypothesis `d i ∣ N` is used. -/
theorem castHom_intCast (hdvd : ∀ i, d i ∣ N) (i : ι) (x : ℤ) :
    ZMod.castHom (hdvd i) (ZMod (d i)) ((x : ℤ) : ZMod N) = ((x : ℤ) : ZMod (d i)) :=
  map_intCast _ x

/-- **Positive direction.** A finite witness over `ZMod N` lifts to a covering of `ℤ`. -/
theorem coversInt_of_coversZMod (hdvd : ∀ i, d i ∣ N) (H : CoversZMod N d r hdvd) :
    CoversInt d r := by
  intro x
  obtain ⟨i, hi⟩ := H ((x : ℤ) : ZMod N)
  rw [castHom_intCast hdvd i x] at hi
  exact ⟨i, (inClass_iff_intCast_eq i x).mpr hi⟩

/-- **Exclusion direction.** A covering of `ℤ` forces the finite check over `ZMod N`
to succeed. Contrapose this to turn a finite UNSAT into a statement about `ℤ`. -/
theorem coversZMod_of_coversInt (hdvd : ∀ i, d i ∣ N) (H : CoversInt d r) :
    CoversZMod N d r hdvd := by
  rw [CoversZMod, ZMod.forall]
  intro x
  obtain ⟨i, hi⟩ := H x
  refine ⟨i, ?_⟩
  rw [castHom_intCast hdvd i x]
  exact (inClass_iff_intCast_eq i x).mp hi

/-- The periodicity bridge. -/
theorem coversInt_iff_coversZMod (hdvd : ∀ i, d i ∣ N) :
    CoversInt d r ↔ CoversZMod N d r hdvd :=
  ⟨coversZMod_of_coversInt hdvd, coversInt_of_coversZMod hdvd⟩

/-- Exclusion, one residue assignment. -/
theorem not_coversInt_of_not_coversZMod (hdvd : ∀ i, d i ∣ N)
    (H : ¬ CoversZMod N d r hdvd) : ¬ CoversInt d r :=
  fun hc => H (coversZMod_of_coversInt hdvd hc)

/-- Exclusion, the shape a SAT UNSAT result actually has: if **no** choice of residues
covers `ZMod N`, then **no** choice of residues covers `ℤ`. -/
theorem forall_not_coversInt (d : ι → ℕ) (hdvd : ∀ i, d i ∣ N)
    (H : ∀ s : ι → ℤ, ¬ CoversZMod N d s hdvd) : ∀ s : ι → ℤ, ¬ CoversInt d s :=
  fun s hc => H s (coversZMod_of_coversInt hdvd hc)

/-- `CoversZMod` depends on each residue only through its class mod `d i`.
This is what lets a SAT search range over `0 ≤ s i < d i` instead of all of `ℤ`. -/
theorem coversZMod_congr (hdvd : ∀ i, d i ∣ N) {r s : ι → ℤ}
    (h : ∀ i, ((r i : ℤ) : ZMod (d i)) = ((s i : ℤ) : ZMod (d i))) :
    CoversZMod N d r hdvd ↔ CoversZMod N d s hdvd := by
  simp only [CoversZMod, h]

/-- **Exclusion, in exactly the shape a finite SAT/enumeration search produces.**
If no residue assignment with `0 ≤ s i < d i` covers `ZMod N`, then no integer
residue assignment whatsoever covers `ℤ`. -/
theorem forall_not_coversInt_of_range (d : ι → ℕ) (hpos : ∀ i, 0 < d i)
    (hdvd : ∀ i, d i ∣ N)
    (H : ∀ s : ι → ℤ, (∀ i, 0 ≤ s i ∧ s i < (d i : ℤ)) → ¬ CoversZMod N d s hdvd) :
    ∀ r : ι → ℤ, ¬ CoversInt d r := by
  intro r hc
  have hdpos : ∀ i, (0 : ℤ) < (d i : ℤ) := fun i => by exact_mod_cast hpos i
  refine H (fun i => r i % (d i : ℤ)) (fun i => ⟨Int.emod_nonneg _ (ne_of_gt (hdpos i)),
    Int.emod_lt_of_pos _ (hdpos i)⟩) ?_
  rw [← coversZMod_congr hdvd (r := r) (fun i => (ZMod.intCast_mod (r i) (d i)).symm)]
  exact coversZMod_of_coversInt hdvd hc

/-- The concrete finite form a program enumerates: it suffices to test the integers
`0, 1, …, N-1`. Equivalent to `coversInt_iff_coversZMod`, but stated in `ℤ`-arithmetic
so a `decide`/`interval_cases` proof can discharge it directly. -/
theorem coversInt_iff_forall_lt (hN : N ≠ 0) (hdvd : ∀ i, d i ∣ N) :
    CoversInt d r ↔ ∀ x : ℤ, 0 ≤ x → x < (N : ℤ) → ∃ i, InClass d r i x := by
  constructor
  · intro H x _ _; exact H x
  · intro H x
    have hNpos : (0 : ℤ) < (N : ℤ) := by exact_mod_cast Nat.pos_of_ne_zero hN
    obtain ⟨i, hi⟩ := H (x % (N : ℤ)) (Int.emod_nonneg x (ne_of_gt hNpos))
      (Int.emod_lt_of_pos x hNpos)
    refine ⟨i, ?_⟩
    have hmod : x % (N : ℤ) % (d i : ℤ) = x % (d i : ℤ) :=
      Int.emod_emod_of_dvd x (Int.natCast_dvd_natCast.2 (hdvd i))
    have hstep : (d i : ℤ) ∣ (x - x % (N : ℤ)) := Int.ModEq.dvd (hmod : Int.ModEq _ _ _)
    have hsum := dvd_add hstep hi
    have hre : (x - x % (N : ℤ)) + (x % (N : ℤ) - r i) = x - r i := by ring
    rwa [hre] at hsum

end Bridge

/-!
## Connection to the `formal-conjectures` vocabulary

`google-deepmind/formal-conjectures` states Erdős 7 over its own `StrictCoveringSystem ℤ`
structure (`FormalConjecturesForMathlib/NumberTheory/CoveringSystem.lean`, Apache-2.0).
That structure is **not** in mathlib, so it is mirrored verbatim below in order to state the
bridge lemmas; when compiled against their package, delete this mirror and import theirs.
-/

namespace FC

open Pointwise

/-- Verbatim mirror of `formal-conjectures`' `CoveringSystem`. -/
structure CoveringSystem (R : Type*) [CommSemiring R] where
  ι : Type
  [fintypeIndex : Fintype ι]
  residue : ι → R
  moduli : ι → Ideal R
  unionCovers : ⋃ i, ({residue i} : Set R) + (moduli i : Set R) = @Set.univ R
  ne_bot : ∀ i, moduli i ≠ ⊥
  ne_top : ∀ i, moduli i ≠ ⊤

/-- Verbatim mirror of `formal-conjectures`' `StrictCoveringSystem`. -/
structure StrictCoveringSystem (R : Type*) [CommSemiring R] extends CoveringSystem R where
  injective_moduli : moduli.Injective

/-- Their pointwise-coset membership is our divisibility. -/
theorem mem_coset_iff_dvd (a n x : ℤ) :
    x ∈ ({a} : Set ℤ) + (Ideal.span ({n} : Set ℤ) : Set ℤ) ↔ n ∣ (x - a) := by
  simp only [Set.singleton_add, Set.mem_image, SetLike.mem_coe, Ideal.mem_span_singleton]
  constructor
  · rintro ⟨y, hy, rfl⟩
    simpa using hy
  · rintro ⟨c, hc⟩
    exact ⟨x - a, ⟨c, hc⟩, by ring⟩

/-- Their ideal-theoretic spelling of "odd" is the numeric one. -/
theorem not_le_span_two_iff_odd (n : ℤ) :
    ¬ (Ideal.span ({n} : Set ℤ) ≤ Ideal.span ({2} : Set ℤ)) ↔ Odd n := by
  rw [Ideal.span_singleton_le_span_singleton, ← even_iff_two_dvd, Int.not_even_iff_odd]

/-- Package concrete `(modulus, residue)` data into their structure. -/
noncomputable def buildStrict {k : ℕ} (a : Fin k → ℤ) (n : Fin k → ℕ)
    (hgt : ∀ i, 1 < n i) (hinj : Function.Injective n)
    (hcov : Erdos7.CoversInt n a) : StrictCoveringSystem ℤ where
  ι := Fin k
  fintypeIndex := inferInstance
  residue := a
  moduli := fun i => Ideal.span ({(n i : ℤ)} : Set ℤ)
  unionCovers := by
    ext x
    simp only [Set.mem_iUnion, Set.mem_univ, iff_true]
    obtain ⟨i, hi⟩ := hcov x
    exact ⟨i, (mem_coset_iff_dvd _ _ _).mpr hi⟩
  ne_bot := by
    intro i h
    rw [Ideal.span_singleton_eq_bot] at h
    have := hgt i
    omega
  ne_top := by
    intro i h
    rw [Ideal.span_singleton_eq_top, Int.isUnit_iff] at h
    have := hgt i
    omega
  injective_moduli := by
    intro i j hij
    apply hinj
    have h1 : (n j : ℤ) ∣ (n i : ℤ) := Ideal.span_singleton_le_span_singleton.mp (le_of_eq hij)
    have h2 : (n i : ℤ) ∣ (n j : ℤ) :=
      Ideal.span_singleton_le_span_singleton.mp (le_of_eq hij.symm)
    exact Nat.dvd_antisymm (Int.natCast_dvd_natCast.mp h2) (Int.natCast_dvd_natCast.mp h1)

/-- **Soundness for a positive answer.** Concrete odd, distinct, `> 1` moduli covering `ℤ`
give exactly the witness `Erdos7.erdos_7`'s right-hand side asks for. Combined with
`Erdos7.coversInt_of_coversZMod`, a finite `ZMod N` witness answers Erdős 7 affirmatively. -/
theorem exists_strictCoveringSystem_odd {k : ℕ} (a : Fin k → ℤ) (n : Fin k → ℕ)
    (hgt : ∀ i, 1 < n i) (hodd : ∀ i, Odd (n i)) (hinj : Function.Injective n)
    (hcov : Erdos7.CoversInt n a) :
    ∃ C : StrictCoveringSystem ℤ, ∀ i, ¬ C.moduli i ≤ Ideal.span {2} ∧ C.moduli i ≠ ⊤ := by
  refine ⟨buildStrict a n hgt hinj hcov, fun i => ⟨?_, (buildStrict a n hgt hinj hcov).ne_top i⟩⟩
  exact (not_le_span_two_iff_odd _).mpr (by exact_mod_cast hodd i)

/-- **Completeness for a negative answer.**
Every abstract odd `StrictCoveringSystem ℤ` comes from concrete data of the form our finite
search enumerates. Needed to claim that finite exclusion results rule out *their* statement,
not merely our concretely-presented families.

Proof route (`ℤ` is a PID, so nothing here is deep, only fiddly):
`C.ι` is a `Fintype`, so pick `k := Fintype.card C.ι` and an equiv `e : Fin k ≃ C.ι`;
each `C.moduli (e i)` is principal (`IsPrincipalIdealRing ℤ`), so
`C.moduli (e i) = Ideal.span {g i}` for a generator `g i`; set `n i := (g i).natAbs`
(`Int.span_natAbs` says the span is unchanged). Then `1 < n i` from `ne_bot` + `ne_top`
via `Ideal.span_singleton_eq_bot` / `Ideal.span_singleton_eq_top` + `Int.isUnit_iff`;
`Odd (n i)` from `not_le_span_two_iff_odd`; injectivity of `n` from
`injective_moduli` plus `Int.span_natAbs`; and `CoversInt` from `unionCovers` +
`mem_coset_iff_dvd`. -/
theorem fc_concrete_of_strictCoveringSystem (C : StrictCoveringSystem ℤ)
    (hodd : ∀ i, ¬ C.moduli i ≤ Ideal.span {2}) :
    ∃ (k : ℕ) (a : Fin k → ℤ) (n : Fin k → ℕ),
      (∀ i, 1 < n i) ∧ (∀ i, Odd (n i)) ∧ Function.Injective n ∧ Erdos7.CoversInt n a := by
  classical
  haveI : Fintype C.ι := C.fintypeIndex
  set e : Fin (Fintype.card C.ι) ≃ C.ι := (Fintype.equivFin C.ι).symm with he
  haveI : ∀ j : C.ι, (C.moduli j).IsPrincipal := fun j => IsPrincipalIdealRing.principal _
  set n : Fin (Fintype.card C.ι) → ℕ :=
    fun i => (Submodule.IsPrincipal.generator (C.moduli (e i))).natAbs with hn
  set a : Fin (Fintype.card C.ι) → ℤ := fun i => C.residue (e i) with ha
  have hspanN : ∀ i, Ideal.span {(n i : ℤ)} = C.moduli (e i) := by
    intro i
    rw [hn]
    change Ideal.span {((Submodule.IsPrincipal.generator (C.moduli (e i))).natAbs : ℤ)} = _
    rw [Int.span_natAbs]
    exact Ideal.span_singleton_generator _
  have hgt : ∀ i, 1 < n i := by
    intro i
    by_contra hle
    rw [not_lt] at hle
    have h01 : n i = 0 ∨ n i = 1 := by omega
    rcases h01 with h0 | h1
    · apply C.ne_bot (e i)
      rw [← hspanN i, h0]
      simp
    · apply C.ne_top (e i)
      rw [← hspanN i, h1]
      simp
  have hodd' : ∀ i, Odd (n i) := by
    intro i
    have h := hodd (e i)
    rw [← hspanN i, not_le_span_two_iff_odd] at h
    exact_mod_cast h
  have hinj : Function.Injective n := by
    intro i j hij
    have hcast : ((n i : ℕ) : ℤ) = ((n j : ℕ) : ℤ) := by exact_mod_cast hij
    have hmod : C.moduli (e i) = C.moduli (e j) := by
      rw [← hspanN i, ← hspanN j, hcast]
    exact e.injective (C.injective_moduli hmod)
  have hcov : Erdos7.CoversInt n a := by
    intro x
    have hx : x ∈ (Set.univ : Set ℤ) := Set.mem_univ x
    rw [← C.unionCovers, Set.mem_iUnion] at hx
    obtain ⟨j, hj⟩ := hx
    refine ⟨e.symm j, ?_⟩
    have hje : e (e.symm j) = j := e.apply_symm_apply j
    have hseteq : (C.moduli j : Set ℤ)
        = (Ideal.span {(n (e.symm j) : ℤ)} : Ideal ℤ) := by
      rw [hspanN (e.symm j), hje]
    rw [hseteq] at hj
    have hdvd := (mem_coset_iff_dvd (C.residue j) (n (e.symm j) : ℤ) x).mp hj
    change (n (e.symm j) : ℤ) ∣ (x - a (e.symm j))
    rw [ha]
    change (n (e.symm j) : ℤ) ∣ (x - C.residue (e (e.symm j)))
    rw [hje]
    exact hdvd
  exact ⟨Fintype.card C.ι, a, n, hgt, hodd', hinj, hcov⟩

/-- **FC-level headline.** Any strict covering system of `ℤ` with all moduli
odd (in `formal-conjectures`' ideal-theoretic vocabulary) yields concrete
distinct odd moduli `> 1` covering `ℤ` whose lcm exceeds `10000` — the
steps-1–5 headline transported to their official statement of Erdős 7. -/
theorem fc_odd_strictCoveringSystem_lcm_gt_10000 (C : StrictCoveringSystem ℤ)
    (hodd : ∀ i, ¬ C.moduli i ≤ Ideal.span {2}) :
    ∃ (k : ℕ) (a : Fin k → ℤ) (n : Fin k → ℕ),
      (∀ i, 1 < n i) ∧ (∀ i, Odd (n i)) ∧ Function.Injective n ∧
      Erdos7.CoversInt n a ∧ 10000 < Finset.univ.lcm n := by
  obtain ⟨k, a, n, hgt, hodd', hinj, hcov⟩ := fc_concrete_of_strictCoveringSystem C hodd
  exact ⟨k, a, n, hgt, hodd', hinj, hcov,
    _root_.odd_covering_lcm_gt_10000 n a hgt hodd' hinj hcov⟩

end FC


/-!
## End-to-end smoke tests

These confirm the definitions are not vacuous and that the whole pipeline
(finite kernel `decide` over `ZMod N`  ⟹  statement about `ℤ`) closes with no
`sorry` and no native-evaluation axiom. `#print axioms` on both results reports
exactly `[propext, Classical.choice, Quot.sound]`.
-/

namespace Smoke

/-- Erdős's classic distinct covering system
`{0 mod 2, 0 mod 3, 1 mod 4, 5 mod 6, 7 mod 12}`. -/
def cd : Fin 5 → ℕ := ![2, 3, 4, 6, 12]
def cr : Fin 5 → ℤ := ![0, 0, 1, 5, 7]

theorem cd_dvd : ∀ i, cd i ∣ 12 := by decide

theorem classic_coversZMod : CoversZMod 12 cd cr cd_dvd := by
  unfold CoversZMod; decide

/-- POSITIVE: a finite `decide` over `ZMod 12` yields a covering of all of `ℤ`. -/
theorem classic_coversInt : CoversInt cd cr :=
  coversInt_of_coversZMod cd_dvd classic_coversZMod

/-- Negative fixture: `{0 mod 3, 0 mod 5}`, which misses `1 mod 15`. -/
def nd : Fin 2 → ℕ := ![3, 5]
def nr : Fin 2 → ℤ := ![0, 0]

theorem nd_dvd : ∀ i, nd i ∣ 15 := by decide

theorem not_coversZMod_15 : ¬ CoversZMod 15 nd nr nd_dvd := by
  unfold CoversZMod; decide

/-- EXCLUSION: a finite `decide` refuting coverage of `ZMod 15` rules out
coverage of all of `ℤ`. -/
theorem not_coversInt_15 : ¬ CoversInt nd nr :=
  not_coversInt_of_not_coversZMod nd_dvd not_coversZMod_15

end Smoke

end Erdos7
