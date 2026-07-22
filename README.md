# Erdős #7: kernel-checked exclusions for the odd covering problem

Lean 4 formalization of known partial results on the Erdős–Selfridge **odd
covering problem** ([Erdős #7](https://www.erdosproblems.com/7)): *does a
covering system of ℤ exist whose moduli are all odd, distinct, and greater
than 1?* The problem is open; this repository proves, sorry-free and
kernel-checked:

```lean
/-- Any covering of ℤ by finitely many congruence classes with distinct
odd moduli > 1 has lcm > 10000. -/
theorem odd_covering_lcm_gt_10000
    {ι : Type} [Fintype ι] (n : ι → ℕ) (a : ι → ℤ)
    (hgt : ∀ i, 1 < n i) (hodd : ∀ i, Odd (n i))
    (hinj : Function.Injective n)
    (hcov : ∀ x : ℤ, ∃ i, (n i : ℤ) ∣ (x - a i)) :
    10000 < Finset.univ.lcm n
```

together with the transport of this statement to the official
`StrictCoveringSystem ℤ` formulation of `erdos_7` in
[google-deepmind/formal-conjectures](https://github.com/google-deepmind/formal-conjectures)
(`Erdos7.FC.fc_odd_strictCoveringSystem_lcm_gt_10000`, `Bridge.lean`).

## What is new here, and what is not

The mathematical content here is **known**: the density/abundancy argument
is folklore, and McNew–Setty (*On the densities of covering numbers and
abundant numbers*, [arXiv:2507.23041](https://arxiv.org/abs/2507.23041))
classified covering numbers up to 10⁶, far beyond this range, with a
Gurobi-based pipeline. The contribution of this repository is epistemic, not
mathematical: these exclusions are **theorems of the Lean kernel**, depending
only on `propext`, `Classical.choice`, and `Quot.sound`, with no solver in
the trusted base and no appeal to unformalized literature. This is not
progress on the open question.

## Contents

| File | What it proves |
|---|---|
| `Erdos7/Density.lean` | Density lemma: covering with divisor moduli > 1 forces `2N ≤ σ₁(N)` |
| `Erdos7/AbundancyFloor.lean` | No odd `N < 945` qualifies; `odd_covering_lcm_ge_945` |
| `Erdos7/Capacity.lean` | CRT capacity certificates; each of the 23 odd abundant `N < 10⁴` excluded |
| `Erdos7/Enumeration.lean` | Kernel-checked enumeration (those 23 are the only candidates); the headline |
| `Erdos7/Bridge.lean` | ℤ ⟺ `ZMod N` periodicity bridge; formal-conjectures transport |
| `Erdos7/AxiomCheck.lean` | `#print axioms` for all 63 published theorems |
| `Erdos7/AxiomAudit.lean` | Automated audit: discovers every theorem in every module from the compiled environment and re-checks its axiom closure, so nothing can slip past the hand-kept list |
| `scripts/axiom_gate.sh` | The gate, run by CI on every push: manifest + audit, failing on any axiom beyond the three, any `sorryAx`, any `_native.*` |

## Check it yourself

Requires [elan](https://github.com/leanprover/elan); the toolchain
(Lean 4.30.0) and mathlib pin are in `lean-toolchain` / `lake-manifest.json`.

```
lake exe cache get      # fetch mathlib build cache
lake build Erdos7       # ~10 min: two long kernel computations
scripts/axiom_gate.sh   # PASS = 63 published + full-library audit, axioms ⊆ {propext, Classical.choice, Quot.sound}
```

The two dominant costs are the 945 abundancy floor (≈80 s) and the 10⁴
enumeration scan (≈100 s), both single closed `decide`s checked by the
kernel. `native_decide` is never used (each use would add a
native-evaluation trust axiom).

## Attribution

The `CoveringSystem`/`StrictCoveringSystem` structures in `Bridge.lean` are
mirrored verbatim from
[formal-conjectures](https://github.com/google-deepmind/formal-conjectures)
(Apache-2.0, The Formal Conjectures Authors), verified field-for-field
against upstream `main` @ `81e700d16ada`.

## License

[Apache 2.0](LICENSE). Copyright 2026 Millennium Research
(Ibby Mian, Shayaan Siddique); developed with Claude.
