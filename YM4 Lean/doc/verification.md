# Verification

The public challenge states `YangMills.wilson_subsequence`. Its proof uses the stronger theorem `YangMills.su2_fixed_observable_continuum_limit`. The results below apply to the November 20, 2026 source fingerprint `3dcd01297c42277f2cf597ad84e6b3913c9e65186cc0277e94d73d77abc2a849`. [Challenge](../Challenge.lean) · [Public proof](../Formulation/WilsonSubsequence.lean) · [Detailed verification record](verification.json)

| Check | Result |
| --- | --- |
| Lean 4.33.1 | The public proof’s local dependency graph contains 12,435 modules. Lean recompiled 64, including both theorem entry points. The other 12,371 matched earlier build artifacts and source hashes. |
| Axioms | Lean reported exactly `Classical.choice`, `Quot.sound`, `propext` for each theorem. The proof environment excludes the challenge and Wightman reconstruction. |
| Con Leche, `--verified` | Accepted all 333,678 grouped declarations in the proof export, including proof values for both continuum theorems. |
| Native adapter using upstream Comparator APIs | Matched 6,088 scoped declarations, including 2,628 theorem types. Checked 2,627 challenge helper proofs for their axiom dependencies. No definition holes. All 13 controls passed. |
| Stock `lake comparator` on exports | Matched the configured public theorem and accepted the solution export with Lean’s default kernel. The CLI ran with sandboxing disabled. |
| Stock sandboxed rebuild | The Windows Lake invocation exited with status 2. Its Bubblewrap sandbox requires Linux namespaces. |

The independent challenge imports only Mathlib and has one intentional placeholder for the theorem being tested. Both Comparator runs target the public statement. The stock CLI used the same solution export with 546 bytes of additional Lean declarations appended. Con Leche also accepted all 333,680 grouped declarations in this longer export. The latest build of all project libraries is recorded under November 18 below. [Comparator instructions](../scripts/comparator/README.md)

## Whole-package scan

The dependency scan covered all 12,588 implementation modules, including optional reconstruction. All 229,207 distinct theorems had proof terms. None depended on the challenge placeholder or on a partial or unsafe declaration. The only axioms reached were `propext`, `Classical.choice` and `Quot.sound`. Lean generated 524 partial recursion helpers for execution. The proof export contained none of them.

Nanoda independently accepted all 342,294 expanded declarations in the same export accepted by Con Leche and stock Comparator. The native Comparator also matched all 6,088 scoped declarations on those exact bytes. [Machine-readable results](verification.json)

## Earlier snapshots

- **November 19, 2026** (`74402798afb1`). Lean compiled all 68 changed or added modules and the three entry modules. The interface check matched 2,069 public declaration types and 662 public definition or opaque bodies across the affected modules.
- **November 18, 2026** (`99eeece7f399`). The full incremental build passed for 12,612 project modules and 21,321 Lake jobs. The native Comparator, Nanoda and Con Leche passed for that snapshot. The detailed record preserves the results and artifact hashes for both earlier snapshots. [Verification data](verification.json)
