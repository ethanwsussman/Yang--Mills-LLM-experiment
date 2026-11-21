import YangMills.Construction.Lattice.OneScaleOperatorBounds
import Mathlib
set_option autoImplicit false
noncomputable section
namespace YangMills.Construction.PeriodicLattice
open ScaledFun
def MaxBallSiteEstimates : Prop :=
  ∀ (d L j N : ℕ) (S : Scales d L j N),
    (∀ (u : Torus d N) (s : ℝ), 0 < s → ∀ x ∈ maxBall (d := d) S.fineMesh s u,
      taxicabDist (x : Torus d N) u ≤ (d : ℝ) * s) ∧
    (∀ (u v : Torus d N) (s s' : ℝ), 0 < s → 0 < s' →
      ∀ U U' : Set (GridPoint d S.fineMesh), U.Nonempty → U'.Nonempty →
        U ⊆ maxBall S.fineMesh s u → U' ⊆ maxBall S.fineMesh s' v →
        taxicabDist u v - (d : ℝ) * (s + s') ≤ siteSetDist U U') ∧
    (∀ u : Torus d N, (maxBall (d := d) S.fineMesh 1 u).Nonempty ∧
      ((maxBall (d := d) S.fineMesh 1 u).ncard : ℝ) ≤ (3 / fineScale L j) ^ d) ∧
    (∀ (ι : Type) [Fintype ι] (u : Torus d N) (f : MultiField d S.fineMesh ι),
      MultiField.SupportedIn f (maxBall S.fineMesh 1 u) →
        ‖f‖ ^ 2 ≤ (Fintype.card ι : ℝ) * 3 ^ d * MultiField.maxNorm f ^ 2) ∧
    (∀ y : GridPoint d S.unitMesh,
      (∀ x ∈ S.fineCell y, x ∈ maxBall S.fineMesh 1 (y : Torus d N)) ∧
      (∀ (μ : Fin d), ∀ x ∈ S.fineCell y,
        x - S.fineMesh.basisStep μ ∈ maxBall S.fineMesh 1 (y : Torus d N)) ∧
      ∀ x : GridPoint d S.fineMesh, (x : Torus d N) ∈ halfOpenCube (y : Torus d N) 2 →
        x ∈ maxBall S.fineMesh 1 ((y : Torus d N) + diagonalOne))
end YangMills.Construction.PeriodicLattice
