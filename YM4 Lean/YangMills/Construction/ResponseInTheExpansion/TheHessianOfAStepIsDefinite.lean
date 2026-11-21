import YangMills.Construction.ResponseInTheExpansion.MaxwellFormOfTheChain
import YangMills.Construction.ResponseInTheExpansion.TowerAtTheParameters
import Mathlib
set_option autoImplicit false
noncomputable section
namespace YangMills.Construction.ResponseInTheExpansion
open BlockAverages LumpContours ColdStepAtMirrorFrames ClusterExpansionOfAStep RenormalizationStepParameters WeightedResponses
variable (Tb : ParameterAssignment) (y : ℝ)
def StepHessianPosDefAt : Prop :=
  ∀ (u n : ℕ) [NeZero n], Tb.n₀ ≤ n →
    (trivialHessian Tb.coupling (ParameterAssignment.stepParameters Tb y).side u n).PosDef
def stepHessianPosDefStatement : Prop := HoldsOnParameterFamilies StepHessianPosDefAt
end YangMills.Construction.ResponseInTheExpansion
end
