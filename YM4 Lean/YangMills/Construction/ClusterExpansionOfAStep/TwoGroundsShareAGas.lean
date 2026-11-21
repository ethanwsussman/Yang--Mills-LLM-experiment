import YangMills.Construction.ClusterExpansionOfAStep.SharedGasOfTwoGrounds
import YangMills.Construction.ClusterExpansionOfAStep.StepAtFixedParameters
import Mathlib
set_option autoImplicit false
noncomputable section
open MeasureTheory
namespace YangMills.Construction.ClusterExpansionOfAStep
open Dobrushin StepGas StepSettings RenormalizationStepParameters TorusFields
def GroundsShareInnerGas : Prop :=
  ∃ rt₀ : ChainParameters → ℝ, (∀ c, 0 < rt₀ c) ∧ ∀ T : ParameterAssignment, T.Admissible →
    T.rt ≤ rt₀ T.toChainParameters →
    ∃ y₀ : ℝ, ∀ y : ℝ, y₀ ≤ y → ∀ R : StepSetup, R.OnParameters T y → R.nextCoupling ≤ 1.01 * R.coupling →
      ∀ (n n' : ℕ) [NeZero n] [NeZero n']
      (G : GasGround R n) (G' : GasGround R n') (Y : TorusSite n) (Y' : TorusSite n') (N : ℕ)
      (A : Finset (TorusSite n)) (A' : Finset (TorusSite n')),
      G.IsAdmissibleGround → G'.IsAdmissibleGround → 16 * R.frameReach ≤ N → GroundsAgreeNear G G' Y Y' N →
      BlockSetsAgreeNear A A' Y Y' N →
      Nonempty (SharedInnerGas G G' Y Y' N (N - R.frameReach - 1) A A')
end YangMills.Construction.ClusterExpansionOfAStep
end
