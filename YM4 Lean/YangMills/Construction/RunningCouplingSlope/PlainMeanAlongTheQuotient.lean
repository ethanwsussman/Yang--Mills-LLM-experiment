import YangMills.Construction.RunningCouplingSlope.PlainSaddlesOnTheWholeLattice
import YangMills.Construction.RunningCouplingSlope.SoftChainOnATower
import Mathlib
set_option autoImplicit false
noncomputable section
namespace YangMills.Construction.RunningCouplingSlope
open Tower Matrices Conventions
def ContourMeanAlongProjection : Prop :=
  ∀ L : ℕ, IsAdmissibleBlockingFactor L → ∀ n k j : ℕ, 0 < n → j < k →
    ∀ c : FullSpace.Edge L k (j + 1), c.IsPositivelyOriented →
      ∀ (W : FullSpace.Edge L k j → ComplexMatrix2) (V : Edge L n k j → ComplexMatrix2),
        (∀ b ∈ FullSpace.doubleCubeLinks L (meshAt L k j) c,
          W b = V (FullSpace.projEdge L n k j b)) →
        FullLattice.contourMean W c = contourMean V (FullSpace.projEdge L n k (j + 1) c)
end YangMills.Construction.RunningCouplingSlope
end
