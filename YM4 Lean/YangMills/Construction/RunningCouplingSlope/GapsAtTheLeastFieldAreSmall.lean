import YangMills.Construction.ClusterExpansionOfAStep.StepAtFixedParameters
import YangMills.Construction.RunningCouplingSlope.ExponentOfAStepAlongACurve
import Mathlib
set_option autoImplicit false
noncomputable section
namespace YangMills.Construction.RunningCouplingSlope
open YangMills.Construction.BlockAverages YangMills.Construction.RenormalizationStepParameters YangMills.Construction.StepSettings YangMills.Construction.TorusFields
def haarGapSumSecondDerivStatement : Prop :=
  ∀ T : ParameterAssignment, T.Admissible → ∃ C q : ℝ, 0 < C ∧ 0 ≤ q ∧
    ∀ (y : ℝ) (R : StepSetup), T.floorMin ≤ y → R.OnParameters T y →
      ∀ (n : ℕ) [NeZero n] (c : Fin 2 → TorusBond n) (X : Fin 2 → imaginaryQuaternions), T.n₀ ≤ n →
        AreUnitVectors X →
        ContDiffAt ℝ 2 (haarGapSumAlongCurve R n c X) 0 ∧
        |iteratedFDeriv ℝ 2 (haarGapSumAlongCurve R n c X) 0 (fun l => Pi.single l 1)| ≤
          C * (n : ℝ) ^ q * R.coupling⁻¹
end YangMills.Construction.RunningCouplingSlope
end
