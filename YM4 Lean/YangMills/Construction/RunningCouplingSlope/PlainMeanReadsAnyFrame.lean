import YangMills.Construction.RunningCouplingSlope.LeastChainOverAField
import Mathlib
set_option autoImplicit false
open scoped Quaternion
noncomputable section
namespace YangMills.Construction
namespace RunningCouplingSlope
def ContourMeanMatchesFrame : Prop :=
  ∀ L : ℕ, Conventions.IsAdmissibleBlockingFactor L → ∀ n k j M : ℕ, 0 < n → j < k → M * L = 2 * L ^ (n + (k - j)) →
    ∀ F : BlockAverages.BlockFrame, F.blockSide = L → (∀ i, F.period j i = M * L) → (∀ i, F.period (j + 1) i = M) →
      ∀ (V : TorusFields.TorusField (M * L)) (U : Tower.Edge L n k j → Matrices.ComplexMatrix2),
        RepresentsAtLevel j U V →
        ∀ (z : Fin 4 → ℤ) (μ : Fin 4),
          contourMean U (PeriodicLattice.Bond.forwardFrom (PeriodicLattice.offsetSite 0 z) μ) =
            SoftAverages.quaternionToMatrix
              (BlockAverages.contourAverage (TorusFields.readAtLevel F j V) (BlockAverages.siteOfCoords (j + 1) z, μ))
end RunningCouplingSlope
end YangMills.Construction
end
