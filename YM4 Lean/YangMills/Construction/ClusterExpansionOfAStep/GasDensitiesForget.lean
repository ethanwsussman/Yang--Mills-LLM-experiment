import YangMills.Construction.ClusterExpansionOfAStep.GasOfASetting
import YangMills.Construction.ClusterExpansionOfAStep.StepAtFixedParameters
import Mathlib
set_option autoImplicit false
noncomputable section
namespace YangMills.Construction.ClusterExpansionOfAStep
open RenormalizationStepParameters StepSettings StepGas TorusFields
def GasDensityForgets : Prop :=
  ∃ rt₀ : ChainParameters → ℝ, (∀ c, 0 < rt₀ c) ∧ ∀ T : ParameterAssignment, T.Admissible → T.rt ≤ rt₀ T.toChainParameters →
    ∃ y₀ : ℝ, ∀ y : ℝ, y₀ ≤ y → ∀ R : StepSetup, R.OnParameters T y → R.nextCoupling ≤ 1.01 * R.coupling →
      ∀ (n n' : ℕ) [NeZero n] [NeZero n']
      (G : GasGround R n) (G' : GasGround R n') (Y : TorusSite n) (Y' : TorusSite n') (N : ℕ),
      G.IsAdmissibleGround → G'.IsAdmissibleGround → 1 ≤ N → GroundsAgreeNear G G' Y Y' N →
      |G.blockDensity Y - G'.blockDensity Y'| ≤ Real.exp (-(T.gasRate * R.coupling) - T.rt * N / 2 ^ 8)
end YangMills.Construction.ClusterExpansionOfAStep
end
