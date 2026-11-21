import YangMills.Construction.ClusterExpansionOfAStep.StepAtFixedParameters
import YangMills.Construction.RunningCouplingSlope.LaplaceOfAStep
import Mathlib
set_option autoImplicit false
noncomputable section
open scoped Topology
namespace YangMills.Construction.RunningCouplingSlope
def LaplaceRemainderIsGaugeFunctionNear : Prop :=
  ∀ T : RenormalizationStepParameters.ParameterAssignment, T.Admissible → ∀ (y : ℝ) (S : StepSettings.StepSetup), T.floorMin ≤ y →
    S.OnParameters T y →
    ∀ (n : ℕ) [NeZero n], T.n₀ ≤ n → n ≤ 4 * S.frameReach + 5 →
      ∀ᶠ p : (TorusFields.TorusSite n → BlockAverages.UnitQuaternion) × TorusFields.TorusField n in
          𝓝 (1, TorusFields.trivialField n),
        laplaceRemainder S n (TorusFields.gaugeTransform p.1 p.2) = laplaceRemainder S n p.2
end YangMills.Construction.RunningCouplingSlope
end
