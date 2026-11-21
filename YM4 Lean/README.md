# The four-dimensional SU(2) Wilson continuum limit and the Osterwalder–Schrader axioms

At each sufficiently fine lattice spacing, choose the least positive bare coupling that gives a prescribed two-point correlation on a reference torus. At those couplings, the centered Wilson plaquette energy has a nontrivial subsequential continuum limit on four-dimensional Euclidean space. Its moments are averages of components satisfying the full Osterwalder–Schrader axioms, including spatial clustering. [Informal theorem and axioms (PDF)](doc/Theorem.pdf) · [Mathlib-only statement](Challenge.lean#L235) · [Lean proof](Formulation/WilsonSubsequence.lean#L14)

## The theorem

For each sufficiently large odd blocking factor $L$, the theorem supplies a reference torus of side $2L^M$ and an interval $0<g_0<\delta$ of physical couplings. Use the fixed smooth radial bump $\chi$ supported in the ball of radius $1/8$ and its translate $\chi_0(x)=\chi(x-3e_1)$. Write $\Phi(f)$ for the centered plaquette energy smeared against $f$. One cutoff threshold works for every $0<g_0<\delta$. At each finer cutoff $K$, the bare coupling $g_K$ is the smallest positive solution of

$$
\mathbb E_{g_K}[\Phi(\chi)\Phi(\chi_0)]
=\frac{9g_0^4}{\pi^4}\int_{\mathbb R^4}\int_{\mathbb R^4}
\frac{\chi(x)\chi_0(y)}{|x-y|^8}\,dy\,dx .
$$

One increasing subsequence of cutoffs $K_j$ gives all of the following conclusions. [Theorem statement](Challenge.lean#L235)

- **Infinite-volume continuum limit.** For every order and every tuple of smooth, compactly supported tests with pairwise disjoint supports, the centered moments converge when one takes infinite volume first and then sends $a_j=L^{-K_j}$ to zero. A single sequence of growing tori gives the same limits.
- **Asymptotic freedom.** The selected couplings obey $g_{K_j}^2\log(1/a_j)\to 3\pi^2/11$.
- **Nontriviality.** Some separated smooth pair has strictly positive covariance, and some separated smooth quadruple has a strictly positive fourth cumulant.
- **Osterwalder–Schrader axioms.** The limiting distributions act on Schwartz tests flat at collisions. They are normalized, continuous and complex linear, satisfy a factorial growth bound, are Euclidean and permutation invariant, and obey reflection reality and positivity. On separated tensors their values are integrals of component Schwinger distributions against a probability measure. Every component satisfies these axioms and spatial clustering. For almost every component there is a separated smooth quadruple with nonzero fourth cumulant. [Axioms](Challenge.lean#L170) · [Component decomposition](Challenge.lean#L216)

The construction identifies the inner limits as moments of infinite-volume lattice states and gives convergence of connected correlations on separated $C^1$ tests. The optional reconstruction theorem supplies scalar Wightman fields for representatives of the canonical components. [Euclidean construction](Formulation/FixedObservableContinuum.lean) · [Optional reconstruction](Reconstruction/FixedObservable.lean)

## Repository layout

| Path | Contents |
| --- | --- |
| [Challenge.lean](Challenge.lean) | Self-contained statement importing only Mathlib. The one `sorry` marks the challenge for Comparator. |
| [Formulation/WilsonSubsequence.lean](Formulation/WilsonSubsequence.lean#L14) | Proof of the SU(2) theorem. The public declaration `YangMills.wilson_subsequence` applies this proof. [Public theorem](Formulation/WilsonSubsequence.lean#L70) |
| [Formulation/](Formulation/) | Fixed-observable coupling, infinite-volume limits, and proof of the public statement. |
| [YangMills/](YangMills/) | Lattice construction, renormalization estimates, Euclidean symmetries, and component decomposition. |
| [Reconstruction/](Reconstruction/) | Optional scalar Wightman reconstruction, with the earlier combined theorems in [Legacy.lean](Reconstruction/Legacy.lean). |
| [doc/](doc/) | Informal theorem in [PDF](doc/Theorem.pdf) and [LaTeX](doc/Theorem.tex), plus the [verification record](doc/verification.md). |
| [comparator.json](comparator.json) and [scripts/comparator/](scripts/comparator/) | Public theorem target, permitted axioms, and tools for reproducing the native comparison. |

## Changing the gauge group

The challenge selects its model with `abbrev selectedGauge := specialUnitary 2`. Changing `2` to `3` gives the SU(3) statement using Mathlib’s matrix group. For SU($N$) in the defining representation, the reference coefficient is $3(N^2-1)$ and the asymptotic limit is $12\pi^2/(11N^2)$. A different closed matrix subgroup can be specified with its real Lie algebra dimension and adjoint Casimir. The supplied proof establishes the SU(2) instance. [Gauge selector](Challenge.lean#L77) · [Matrix subgroup constructor](Challenge.lean#L55) · [Solution-side definitions](Formulation/WilsonDefinitions.lean#L77)

## Build and verification

The project pins Lean 4.33.1 and its Mathlib revision. From the repository root run

```sh
lake exe cache get
lake build
```

This builds the Euclidean theorem and its independent challenge. Run `lake build Reconstruction` for the optional scalar-field reconstruction. To check every library explicitly, run

```sh
lake build YangMills Formulation Challenge Reconstruction
```

To inspect the assumptions, open a Lean file in the project containing

```lean
import Formulation.WilsonSubsequence
#print axioms YangMills.wilson_subsequence
#print axioms YangMills.su2_fixed_observable_continuum_limit
```

The allowed foundational axioms are `propext`, `Classical.choice`, and `Quot.sound`. The verification record identifies the exact sources and proof exports covered by each check. [Verification record](doc/verification.md) · [Comparator instructions](scripts/comparator/README.md)

The repository contains 2,249,256 lines of Lean across the project and comparator tools, including 29,617 lines in the optional reconstruction library. The three original archives contained 3,118,662 lines. Counting the entire release gives a 27.88% reduction in physical lines and a 19.00% reduction in nonblank lines.

## AI assistance

**Disclaimer** *This repository contains work-in-progress, written largely by LLM. Its content has not been satisfactorily vetted. All claims should be understood as tentative, pending verification.* Novel mathematical ideas should be attributed to Claude, under the guidance of one of us [LA]. Older mathematical ideas may not be attributed properly now, but should be in due course.
