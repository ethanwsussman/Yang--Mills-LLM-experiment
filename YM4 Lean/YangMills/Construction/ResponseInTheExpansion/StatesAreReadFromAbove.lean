import YangMills.Construction.ResponseInTheExpansion.LocalSizesOfTheChain
import Mathlib
set_option autoImplicit false
noncomputable section
open MeasureTheory
namespace YangMills.Construction.ResponseInTheExpansion
open YangMills.Construction.WeightedResponses
def upperSigmaDeterminesStatesStatement : Prop :=
  ∀ (ℓ : TorusLumps.StepParameters), ℓ.Admissible → ∀ (T : StageTower ℓ) (t d n : ℕ) [NeZero n],
    upperSigma T t d n ≤ markedSampleMeasurableSpace ℓ (t + d) n ∧
    Measurable[upperSigma T t d n] (stageState T (t + d) n)
end YangMills.Construction.ResponseInTheExpansion
end
