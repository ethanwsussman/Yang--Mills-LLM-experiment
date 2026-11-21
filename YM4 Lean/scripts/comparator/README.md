# Comparing the Wilson continuum statement

The public target is `YangMills.wilson_subsequence`. The native adapter compares the independent challenge with the module that proves it, using the official Lake `compareAt` and `checkAxioms` APIs. The frozen scope covers the 6,086 declarations reached through the statement and its mathematical definitions, together with `Quot.ind` and `propext`. The adapter compares theorem types and definition bodies and checks the axiom dependencies of the proofs. The challenge has one intentional placeholder. [Challenge](../../Challenge.lean) · [Proof](../../Formulation/WilsonSubsequence.lean) · [Recorded results](../../doc/verification.json)

## Build fresh exports and compare them

Use Python 3.11 or newer and Elan's `lean` and `lake` on your path. The proof project pins Lean 4.33.1. The adapter in this directory pins Lean 4.35.0-rc3, which supplies the comparison APIs. Start with an independent copy of the reference repository when checking another solution.

Build the matching declaration exporter in a sibling checkout. These commands start in the root of this repository and end in the exporter checkout.

```sh
git clone https://github.com/leanprover/lean4export.git ../lean4export
git -C ../lean4export checkout --detach 15f6055e299ad5b89345e533cc2192f4cc00f659
cd ../lean4export
elan toolchain install leanprover/lean4:v4.33.1
elan run leanprover/lean4:v4.33.1 lake build lean4export
```

Return to the root of this repository and run

```sh
lake exe cache get
python scripts/verify-comparator.py --exporter ../lean4export/.lake/build/bin/lean4export
```

The script reads both module names from the reference repository's configuration. It compiles `Challenge.lean` with only the pinned dependencies, then builds and exports the proof directly from `Formulation.WilsonSubsequence`. The solution export includes the public theorem and the stronger `YangMills.su2_fixed_observable_continuum_limit` proof. Allow at least 7 GB beyond the build cache for the two exports. The script writes them to a new temporary directory. Use `--work PATH` to choose another location or `--candidate PATH` to select another solution checkout. [Comparator configuration](../../comparator.json)

## Reuse existing exports

From the repository root, run the following with paths to a separately compiled and exported challenge and solution.

```sh
python scripts/verify-comparator.py --exports PATH_TO_CHALLENGE.ndjson PATH_TO_SOLUTION.ndjson
```

The script checks the frozen scope's SHA-256 before passing it and the two exports to the adapter. Reusing exports runs comparison only. To check another formulation, regenerate the scope for its full declaration closure.

## Test the adapter

From this directory, run

```sh
lake build compare_source_statements
lake env python run_source_controls.py
```

The 13 controls exercise matching and changed theorem types, mathematical definitions, coverage, axiom permissions, and helper proofs. They include acceptance of a different valid helper proof and rejection of a helper that depends on the admitted challenge root.

## Scope of verification

This native procedure runs trusted source on the local host. The included comparison checks the statement and axiom dependencies. The verification record identifies the source snapshot and serialized proof export checked by both independent kernels. A stock sandboxed Comparator rebuild remains outstanding. [Upstream Comparator](https://github.com/leanprover/comparator) · [Verification record](../../doc/verification.json)
