import YangMills.Construction.ClusterExpansionOfAStep.FamiliesOfSpins
import Mathlib
set_option autoImplicit false
noncomputable section
open MeasureTheory
namespace YangMills.Construction.ClusterExpansionOfAStep
open BlockAverages LumpContours ColdStepAtMirrorFrames StepCosts StepGas StepSettings RenormalizationStepParameters TorusFields TorusLumps
def FamilyCaseSumEqIntegral : Prop :=
  ∀ T : ParameterAssignment, T.Admissible → ∃ y₀ : ℝ, ∀ y : ℝ, y₀ ≤ y → ∀ R : StepSetup, R.OnParameters T y →
    R.nextCoupling ≤ 1.01 * R.coupling →
    ∀ (n : ℕ) [NeZero n] (G : GasGround R n), G.IsAdmissibleGround →
      ∀ (F : CaseFunctional R n), IsCaseFunctional F → Measurable (G.gasIntegrand F) → ∀ Γ,
        G.IsPairwiseFarApart Γ →
        ∑ b : BaseChoice R.params.side n, G.caseIntegral F (G.familyBadBonds Γ) (G.familySites Γ) b =
          ENNReal.ofReal (R.functional (n * R.params.side) (trivialField (n * R.params.side))) *
            ENNReal.ofReal (∏ X ∈ chainComponents R.nextRange G.state.1, coarseFactor G.coarse G.state X) *
            ∫⁻ τ, G.gasIntegrand F (valuesOn Γ τ) ∂Measure.pi (fun i : Γ => G.spinStateMeasure i)
end YangMills.Construction.ClusterExpansionOfAStep
end
