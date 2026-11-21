import YangMills.Construction.ParameterData.ShapesOfAPair
import YangMills.Construction.ResponseInTheExpansion.ConnectedFunctionsOfTheExpansion
import Mathlib
set_option autoImplicit false
noncomputable section
namespace YangMills.Construction.TotalDensitiesGiveASystem
def BumpPairIsSeparatedTuple : Prop :=
  ∀ (P : TorusLumps.StepParameters) (m : ℕ) (n : ℝ), 1 ≤ P.side → 1 ≤ m → 0 < n →
    40 * n ≤ PeriodicLattice.torusSide P.side m →
    ResponseInTheExpansion.IsSeparatedTestTuple P m n (1 / 4)
        ![TrajectoryData.firstBump P.side m n 0, TrajectoryData.translatedBump P.side m n 0] ∧
      WeightedResponses.IsNormalizedPairAt P m n (1 / 4) (TrajectoryData.firstBump P.side m n 0)
        (TrajectoryData.translatedBump P.side m n 0) ∧
      (10 : ℝ) ^ (-8 : ℤ) * (1 / 4) ^ 2 ≤
        TestFunctions.inverseEighthKernelTorus (TrajectoryData.firstBump P.side m n 0) (TrajectoryData.translatedBump P.side m n 0)
end YangMills.Construction.TotalDensitiesGiveASystem
end
