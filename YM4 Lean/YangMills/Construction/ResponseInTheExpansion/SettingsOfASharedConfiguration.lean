import YangMills.Construction.ClusterExpansionOfAStep.LocalityOfTheDensities
import YangMills.Construction.ClusterExpansionOfAStep.SharedGasOfTwoGrounds
import YangMills.Construction.ResponseInTheExpansion.ResponseInASetting
import Mathlib
set_option autoImplicit false
noncomputable section
open MeasureTheory
namespace YangMills.Construction.ResponseInTheExpansion
open StepGas StepSettings RenormalizationStepParameters TorusFields WeightedResponses
def SharedConfigurationSettingsAgree : Prop :=
  ∀ T : ParameterAssignment, T.Admissible → ∃ y₀ : ℝ, ∀ y : ℝ, y₀ ≤ y → ∀ R : StepSetup, R.OnParameters T y →
    R.nextCoupling ≤ 1.01 * R.coupling →
    ∀ (n n' : ℕ) [NeZero n] [NeZero n'] (G : GasGround R n) (G' : GasGround R n')
      (Y : TorusSite n) (Y' : TorusSite n') (N : ℕ)
      (g : SharedInnerGas G G' Y Y' N (N - R.frameReach - 1) ∅ ∅) (τ : g.Config),
      G.IsAdmissibleGround → G'.IsAdmissibleGround → 16 * R.frameReach ≤ N →
      GroundsAgreeNear G G' Y Y' N → G.pairConstraint.IsAdmissible (g.extendFirst τ) →
      SettingsAgreeAwayFromFrames (configSetting G (g.extendFirst τ)) (configSetting G' (g.extendSecond τ)) Y Y' N
end YangMills.Construction.ResponseInTheExpansion
end
