import YangMills.Construction.Lattice.OneScaleOperatorBounds
import Mathlib
set_option autoImplicit false
noncomputable section
namespace YangMills.Construction.PeriodicLattice
def ComplementLaplacianBlockBound : Prop :=
  ∀ (d L j N : ℕ) (S : Scales d L j N) (f : SiteFun d S.fineMesh),
    ∃ κ : GridPoint d S.unitMesh → ℝ, ∀ y : GridPoint d S.unitMesh,
      (∀ x ∈ S.fineCell y,
        discreteLaplacian S.fineMesh (S.singleScaleGaugeProjCompl f) x = κ y) ∧
      |κ y| ≤ 4 ^ d * Real.sqrt (2 * (d : ℝ)) *
        ‖MultiField.restrictTo (maxBall S.fineMesh 1 (y : Torus d N))
          (discreteGrad S.fineMesh (S.singleScaleGaugeProjCompl f))‖
end YangMills.Construction.PeriodicLattice
