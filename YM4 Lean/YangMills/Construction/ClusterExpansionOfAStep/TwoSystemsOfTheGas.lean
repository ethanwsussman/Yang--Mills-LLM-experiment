import YangMills.Construction.ClusterExpansionOfAStep.ClassesOfTwoGrounds
import YangMills.Construction.ClusterExpansionOfAStep.StepAtFixedParameters
import Mathlib
set_option autoImplicit false
noncomputable section
open MeasureTheory
namespace YangMills.Construction.StepGas
open RenormalizationStepParameters StepSettings TorusLumps TorusFields
def ExpectationsCloseOfGroundsAgreeNear : Prop :=
  ∃ rt₀ : ChainParameters → ℝ, (∀ c, 0 < rt₀ c) ∧ ∀ T : ParameterAssignment, T.Admissible → T.rt ≤ rt₀ T.toChainParameters →
    ∃ y₀ : ℝ, ∀ y : ℝ, y₀ ≤ y → ∀ S : StepSetup, S.OnParameters T y → S.nextCoupling ≤ 1.01 * S.coupling →
      ∀ (n n' : ℕ) [NeZero n] [NeZero n']
      (G : GasGround S n) (G' : GasGround S n') (Y : TorusSite n) (Y' : TorusSite n') (N : ℕ)
      (A : Finset (TorusSite n)) (A' : Finset (TorusSite n')) (F : G.Config → ℝ) (F' : G'.Config → ℝ),
      G.IsAdmissibleGround → G'.IsAdmissibleGround → 16 * S.frameReach ≤ N → GroundsAgreeNear G G' Y Y' N →
      BlockSetsAgreeNear A A' Y Y' N →
      G.ReadsComponentsAt Y F → G'.ReadsComponentsAt Y' F' →
      (∀ σ σ', ComponentsMatch G G' Y Y' N σ σ' → F σ = F' σ') →
      |G.expectation A F - G'.expectation A' F'| ≤ Real.exp (-(2 * T.gasRate * S.coupling) - T.rt * N / 2 ^ 8)
end YangMills.Construction.StepGas
end
