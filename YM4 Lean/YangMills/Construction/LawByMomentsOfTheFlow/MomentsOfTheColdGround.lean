import YangMills.Construction.LawByMomentsOfTheFlow.WindowOfTheLaw
import Mathlib
set_option autoImplicit false
noncomputable section
open MeasureTheory
namespace YangMills.Construction.MomentLaw
def coldGroundMomentsAt (T : RenormalizationStepParameters.ParameterAssignment) (y : ℝ) : Prop :=
  ∀ q : ℕ, ∃ C : ℝ, 0 ≤ C ∧ ∀ (R : StepSettings.StepSetup), R.OnParameters T y → 0 < R.coupling →
    ∀ (n : ℕ) [NeZero n], T.n₀ ≤ n → ∀ V : TorusFields.TorusField n,
    TorusFields.IsCold T.threshold V →
      IsProbabilityMeasure (coldFreeLaw R V) ∧
      (∀ᵐ η ∂(coldFreeLaw R V), ∀ b, StepSettings.coordNorm (η b) < R.ballRadius) ∧
      ∀ b, ∫⁻ η, ENNReal.ofReal (StepSettings.coordNorm (η b) ^ (2 * q)) ∂(coldFreeLaw R V) ≤
        ENNReal.ofReal (C * (R.coupling ^ q)⁻¹)
def coldGroundMomentsStatement : Prop :=
  ResponseInTheExpansion.HoldsOnParameterFamilies coldGroundMomentsAt
end YangMills.Construction.MomentLaw
end
