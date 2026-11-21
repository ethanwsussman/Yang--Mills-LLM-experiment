import YangMills.Construction.ClusterExpansionOfAStep.MarkedIntegralsOfAStep
import YangMills.Construction.ClusterExpansionOfAStep.StepAtFixedParameters
import YangMills.Construction.RunningCouplingSlope.LaplaceOfAStep
import YangMills.Construction.RunningCouplingSlope.TestOfATotal
import Mathlib
set_option autoImplicit false
noncomputable section
namespace YangMills.Construction.RunningCouplingSlope
def LaplaceRemainderHessianClose : Prop :=
  ∃ rt₀ : RenormalizationStepParameters.ChainParameters → ℝ, (∀ l, 0 < rt₀ l) ∧ ∀ T : RenormalizationStepParameters.ParameterAssignment, T.Admissible →
    T.rt ≤ rt₀ T.toChainParameters →
    ∃ C p : ℝ, 0 < C ∧ 0 ≤ p ∧ ∀ (y : ℝ) (R : StepSettings.StepSetup), T.floorMin ≤ y → R.OnParameters T y →
      R.IsSymmetricWeight →
      ∀ (n : ℕ) [NeZero n], T.n₀ ≤ n → n ≤ 4 * R.frameReach + 5 →
        C * (n : ℝ) ^ p * R.coupling ^ (-(1 / 2) : ℝ) ≤ min (T.lam / 2) 1 →
        SlopeCoefficient.IsGaugeFunctionNear (laplaceRemainder R) n ∧
        ∀ (c c' : TorusFields.TorusBond n) (X X' : BlockAverages.imaginaryQuaternions), ‖X‖ = 1 → ‖X'‖ = 1 →
          |SlopeCoefficient.hessianAtTrivial (laplaceRemainder R) n c c' X X' -
              SlopeCoefficient.hessianAtTrivial
                (SlopeCoefficient.stepGaugeTotal T.coupling T.ρA T.side R.depth) n c c' X X' -
              SlopeCoefficient.hessianAtTrivial (densityAtMinimizer R) n c c' X X'| ≤
            C * (n : ℝ) ^ p * R.coupling ^ (-(1 / 2) : ℝ)
end YangMills.Construction.RunningCouplingSlope
end
