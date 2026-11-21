import YangMills.Construction.LawByMomentsOfTheFlow.FormsOfTheLaw
import Mathlib
set_option autoImplicit false
noncomputable section
namespace YangMills.Construction.MomentLaw
variable (Tb : RenormalizationStepParameters.ParameterAssignment) (y : ℝ)
def stepMinimumAt : Prop :=
  ∀ (u n : ℕ) [NeZero n], Tb.n₀ ≤ n →
    (∀ (W : TorusFields.TorusBond (n * (RenormalizationStepParameters.ParameterAssignment.stepParameters Tb y).side) → ℝ)
        (B : TorusFields.TorusBond n → ℝ),
      WeightedResponses.maxwellForm Tb.coupling (RenormalizationStepParameters.ParameterAssignment.stepParameters Tb y).side (u + 1) B B ≤
        WeightedResponses.maxwellForm Tb.coupling (RenormalizationStepParameters.ParameterAssignment.stepParameters Tb y).side u W W +
          Tb.coupling * ∑ c : TorusFields.TorusBond n,
            (contourAverage (RenormalizationStepParameters.ParameterAssignment.stepParameters Tb y).side W c - B c) ^ 2) ∧
    ∀ B : TorusFields.TorusBond n → ℝ,
      WeightedResponses.maxwellForm Tb.coupling (RenormalizationStepParameters.ParameterAssignment.stepParameters Tb y).side (u + 1) B B =
        WeightedResponses.maxwellForm Tb.coupling (RenormalizationStepParameters.ParameterAssignment.stepParameters Tb y).side u
            (WeightedResponses.responseMap Tb.coupling Tb.ρA (RenormalizationStepParameters.ParameterAssignment.stepParameters Tb y).side u B)
            (WeightedResponses.responseMap Tb.coupling Tb.ρA (RenormalizationStepParameters.ParameterAssignment.stepParameters Tb y).side u B) +
          Tb.coupling * ∑ c : TorusFields.TorusBond n,
            (contourAverage (RenormalizationStepParameters.ParameterAssignment.stepParameters Tb y).side
              (WeightedResponses.responseMap Tb.coupling Tb.ρA (RenormalizationStepParameters.ParameterAssignment.stepParameters Tb y).side u B) c
              - B c) ^ 2
def stepMinimumStatement : Prop := ResponseInTheExpansion.HoldsOnParameterFamilies stepMinimumAt
end YangMills.Construction.MomentLaw
end
