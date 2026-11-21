import YangMills.Construction.ClusterExpansionOfAStep.CumulantsOfTheKernelsAtMovedBonds
import YangMills.Construction.ResponseInTheExpansion.LocalSizesOfTheChain
import Mathlib
set_option autoImplicit false
noncomputable section
open scoped Quaternion
namespace YangMills.Construction.ResponseInTheExpansion
open YangMills.Construction.TorusFields YangMills.Construction.TorusLumps YangMills.Construction.RenormalizationStepParameters YangMills.Construction.MarkedIntegrals YangMills.Construction.WeightedResponses
open Classical
variable (Tb : ParameterAssignment) (y : ℝ)
def coldBallDeviationMeasurableAt : Prop :=
  ∃ x₀ : ℝ, ∀ (T : StageTower (Tb.stepParameters y)) (β : ℝ) (k n : ℕ) [NeZero n] (nn : ℝ) (j : ℕ) (o : TorusSite n)
    (b : TorusBond (n * (Tb.stepParameters y).side)),
    IsLocalChainAbove Tb y T β k n nn x₀ → (Tb.stepParameters y).side ∣ n → j < 2 * localChainDepth (Tb.stepParameters y) β k →
    b ∈ chartBondsInBlocks (Tb.stepParameters y).side (supBall o ((localBlockSide (Tb.stepParameters y) β k : ℝ) / 8)) →
    MeasurableQuaternion fun p : TorusField n × TorusField (n * (Tb.stepParameters y).side) =>
      if IsColdOnBall (Tb.stepParameters y).threshold p.1 o (localBlockSide (Tb.stepParameters y) β k) then
        (stepDeviation T (k + j) p.1 p.2 b : ℍ[ℝ]) else 0
def coldBallDeviationMeasurableStatement : Prop := HoldsOnParameterFamilies coldBallDeviationMeasurableAt
end YangMills.Construction.ResponseInTheExpansion
end
