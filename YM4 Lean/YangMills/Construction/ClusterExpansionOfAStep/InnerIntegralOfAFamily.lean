import YangMills.Construction.ClusterExpansionOfAStep.FamiliesOfSpins
import Mathlib
set_option autoImplicit false
noncomputable section
open MeasureTheory
namespace YangMills.Construction.ClusterExpansionOfAStep
open BlockAverages RenormalizationStepParameters StepSettings StepGas SpinFamilies TorusLumps TorusFields
def FamilyInnerLintegral : Prop :=
  ∀ T : ParameterAssignment, T.Admissible → ∃ y₀ : ℝ, ∀ y : ℝ, y₀ ≤ y → ∀ R : StepSetup, R.OnParameters T y →
    R.nextCoupling ≤ 1.01 * R.coupling →
    ∀ (n : ℕ) [NeZero n] (G : GasGround R n), G.IsAdmissibleGround →
      ∀ (F : CaseFunctional R n), IsCaseFunctional F → ∀ Γ, G.IsPairwiseFarApart Γ → ∀ (c : FamilyState G Γ)
        (ν : G.state.unlabelled (G.familySites Γ) → R.labels.Ω),
        (∀ (i : Γ) (z : TorusSite (n * R.params.side)) (hz : z ∈ i.1.1.2) (hr : z ∈ G.state.unlabelled (G.familySites Γ)),
          ν ⟨z, hr⟩ = (c i).2.1 ⟨z, hz⟩) →
        ∫⁻ W, G.caseIntegrand F (G.familyBadBonds Γ) (G.familySites Γ) (G.familySetting c).bases
            (G.overwriteField c W) ν ∂fieldHaar (n * R.params.side) =
          ENNReal.ofReal (R.functional (n * R.params.side) (trivialField (n * R.params.side))) *
            ENNReal.ofReal (∏ X ∈ chainComponents R.nextRange G.state.1, coarseFactor G.coarse G.state X) *
            ((∏ i : Γ, G.allowedActivity i.1 (c i)) *
              (G.familySetting c).settingIntegral F (G.familyBadBonds Γ))
end YangMills.Construction.ClusterExpansionOfAStep
end
