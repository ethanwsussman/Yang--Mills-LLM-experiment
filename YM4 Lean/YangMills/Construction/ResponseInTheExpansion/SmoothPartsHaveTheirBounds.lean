import YangMills.Construction.ResponseInTheExpansion.ColdRegimeBounds
import YangMills.Construction.ResponseInTheExpansion.TotalOfTheResponseFormDefs
import Mathlib
set_option autoImplicit false
noncomputable section
namespace YangMills.Construction.ResponseInTheExpansion
open ColdStepAtMirrorFrames Interpolation RenormalizationStepParameters StepSettings WeightedResponses
def smoothTermsBoundsStatement : Prop :=
  ∀ T : ParameterAssignment, T.Admissible → T.ColdStepHolds → T.HoldsFrom ColdRegimeEstimatesAt →
    ∃ C y₀ : ℝ, 0 ≤ C ∧ ∀ y : ℝ, y₀ ≤ y → ∀ (R : StepSetup) (A : ResponseSetup R), R.OnParameters T y → |A.coeff| ≤ 2 →
    TermBounds R.params (C * R.coupling ^ (-(3 / 2) : ℝ)) (C * R.coupling ^ (-(3 / 2) : ℝ))
      (C * R.coupling ^ (-(3 / 2) : ℝ)) (frameTerm A) ∧
    TermBounds R.params (C / R.coupling) (C / R.coupling) (C / R.coupling) (linearTerm A) ∧
    TermBounds R.params (C * R.coupling ^ (-(1 / 2) : ℝ)) (C * R.coupling ^ (-(1 / 2) : ℝ))
      (C * R.coupling ^ (-(1 / 2) : ℝ)) (incrementTerm A) ∧
    TermBounds R.params (C * R.coupling ^ (-(3 / 2) : ℝ)) (C * R.coupling ^ (-(3 / 2) : ℝ))
      (C * R.coupling ^ (-(3 / 2) : ℝ)) (scoreTailTerm A)
end YangMills.Construction.ResponseInTheExpansion
end
