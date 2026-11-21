import YangMills.Construction.ResponseInTheExpansion.ColdRegimeBounds
import YangMills.Construction.ResponseInTheExpansion.TotalOfTheResponseFormDefs
import YangMills.Construction.SummableBoundsOfTheFlow.NumbersOfFamilies
import Mathlib
set_option autoImplicit false
noncomputable section
namespace YangMills.Construction.ResponseInTheExpansion
open ColdStepAtMirrorFrames FamilyNorms StepSettings RenormalizationStepParameters TorusLumps WeightedResponses
def meanOfFamilyAtStepStatement : Prop :=
  ∀ T : ParameterAssignment, T.Admissible → T.HoldsFrom ColdRegimeEstimatesAt → ∃ C y₀ : ℝ, 0 ≤ C ∧
    ∀ y : ℝ, y₀ ≤ y → ∀ R : StepSetup, R.OnParameters T y →
    ∀ (ε : ℝ) (h : LocalDensity), 0 < ε → ColdDensityBounds R.params ε (ε / T.η₃) h →
      SumInvariantUnderIsometries R.params h →
      TermBounds R.params (2⁻¹ ^ 5 * ε) (2⁻¹ ^ 5 * (ε / T.η₃)) (2⁻¹ ^ 4 * ε)
        (densityOfTopFamily R.params.side R.depth (blockConditionalMean R h)) ∧
      ∃ v, HasUnitPlaneValue (densityOfTopFamily R.params.side R.depth (blockConditionalMean R h)) v ∧
        |v| ≤ C * ε * R.coupling ^ (-(1 / 2) : ℝ)
end YangMills.Construction.ResponseInTheExpansion
end
