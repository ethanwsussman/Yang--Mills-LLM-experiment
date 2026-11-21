import YangMills.Construction.ClusterExpansionOfAStep.FamiliesOfSpins
import Mathlib
set_option autoImplicit false
noncomputable section
namespace YangMills.Construction.ClusterExpansionOfAStep
open StepSettings StepGas RenormalizationStepParameters StepCosts TorusFields
def NonzeroCaseBasesAreGroundOffsets : Prop :=
  ∀ T : ParameterAssignment, T.Admissible → ∃ y₀ : ℝ, ∀ y : ℝ, y₀ ≤ y → ∀ R : StepSetup, R.OnParameters T y →
    R.nextCoupling ≤ 1.01 * R.coupling →
    ∀ (n : ℕ) [NeZero n] (G : GasGround R n), G.IsAdmissibleGround →
      ∀ (F : CaseFunctional R n) Γ, G.IsPairwiseFarApart Γ → ∀ (b : BaseChoice R.params.side n)
        (W : TorusField (n * R.params.side)) (ν : G.state.unlabelled (G.familySites Γ) → R.labels.Ω),
        G.caseIntegrand F (G.familyBadBonds Γ) (G.familySites Γ) b W ν ≠ 0 → ∃ o, b = G.basesOfOffsets Γ o
end YangMills.Construction.ClusterExpansionOfAStep
end
