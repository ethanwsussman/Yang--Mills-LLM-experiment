import YangMills.Construction.ResponseInTheExpansion.MaxwellFormOfTheChain
import YangMills.Construction.ResponseInTheExpansion.TowerAtTheParameters
import Mathlib
set_option autoImplicit false
noncomputable section
namespace YangMills.Construction.ResponseInTheExpansion
open BlockAverages ColdStepAtMirrorFrames RenormalizationStepParameters TorusFields WeightedResponses
variable (Tb : ParameterAssignment) (y : ℝ)
def StepHessianLowerBoundAt : Prop :=
  ∃ lam : ℝ, 0 < lam ∧ ∀ (u n : ℕ) [NeZero n], Tb.n₀ ≤ n →
    (trivialHessian Tb.coupling (Tb.stepParameters y).side u n).PosDef ∧
    ∀ v : ↥(chordBonds (finiteCells (torusFrame (Tb.stepParameters y).side u n))) → ℝ,
      lam * ∑ b, v b ^ 2 ≤ v ⬝ᵥ (trivialHessian Tb.coupling (Tb.stepParameters y).side u n).mulVec v
def stepHessianLowerBoundStatement : Prop := HoldsOnParameterFamilies StepHessianLowerBoundAt
end YangMills.Construction.ResponseInTheExpansion
end
