import YangMills.Construction.ClusterExpansionOfAStep.FamiliesOfSpins
import Mathlib
set_option autoImplicit false
noncomputable section
open MeasureTheory
namespace YangMills.Construction.ClusterExpansionOfAStep
open BlockAverages RenormalizationStepParameters StepSettings StepGas SpinFamilies TorusLumps TorusFields
def FamilyRecoversState : Prop :=
  ∀ T : ParameterAssignment, T.Admissible → ∃ y₀ : ℝ, ∀ y : ℝ, y₀ ≤ y → ∀ R : StepSetup, R.OnParameters T y →
    R.nextCoupling ≤ 1.01 * R.coupling →
    ∀ (n : ℕ) [NeZero n] (G : GasGround R n), G.IsAdmissibleGround →
      ∀ Γ, G.IsPairwiseFarApart Γ → ∀ c : FamilyState G Γ, (∀ i : Γ, G.IsAllowed i.1.1 (c i)) →
        ∀ η, (G.familySetting c).InBalls η → ∀ ν : G.state.unlabelled (G.familySites Γ) → R.labels.Ω,
          (∀ (i : Γ) (z : TorusSite (n * R.params.side)) (hz : z ∈ i.1.1.2)
              (hr : z ∈ G.state.unlabelled (G.familySites Γ)),
            ν ⟨z, hr⟩ = (c i).2.1 ⟨z, hz⟩) →
          coarseStateOf R G.cut ((G.familySetting c).field η) (G.familySites Γ)
            (G.state.fillLabels (G.familySites Γ) ν) (G.familyBadBonds Γ) (G.familySetting c).bases = G.state
end YangMills.Construction.ClusterExpansionOfAStep
end
