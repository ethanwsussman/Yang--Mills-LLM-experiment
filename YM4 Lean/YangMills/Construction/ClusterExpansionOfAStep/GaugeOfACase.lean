import YangMills.Construction.ClusterExpansionOfAStep.FamiliesOfSpins
import YangMills.Construction.ClusterExpansionOfAStep.FreeBondsInCoordinates
import Mathlib
set_option autoImplicit false
noncomputable section
open MeasureTheory
namespace YangMills.Construction
namespace ClusterExpansionOfAStep
open BlockAverages RenormalizationStepParameters StepSettings StepGas SpinFamilies TorusLumps TorusFields
def RestIntegrandGaugeInvariant : Prop :=
  ∀ T : ParameterAssignment, T.Admissible → ∃ y₀ : ℝ, ∀ y : ℝ, y₀ ≤ y → ∀ R : StepSetup, R.OnParameters T y →
    R.nextCoupling ≤ 1.01 * R.coupling →
    ∀ (n : ℕ) [NeZero n] (G : GasGround R n), G.IsAdmissibleGround →
      ∀ (F : CaseFunctional R n), IsCaseFunctional F → ∀ Γ, G.IsPairwiseFarApart Γ → ∀ (c : FamilyState G Γ)
        (ν : G.state.unlabelled (G.familySites Γ) → R.labels.Ω) (g : TorusSite (n * R.params.side) → UnitQuaternion),
        IsBlockGauge R.params.side (G.freeBlocks Γ) g →
        ∀ W, G.restIntegrand F (G.familyBadBonds Γ) (G.familySites Γ) (G.familySetting c).bases
            (G.familySetting c).free ν (gaugeTransform g W) =
          G.restIntegrand F (G.familyBadBonds Γ) (G.familySites Γ) (G.familySetting c).bases
            (G.familySetting c).free ν W
end ClusterExpansionOfAStep
end YangMills.Construction
end
