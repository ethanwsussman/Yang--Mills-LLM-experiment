import YangMills.Construction.ClusterExpansionOfAStep.ParametersOfARenormalizationStep
import YangMills.Construction.LawOnABoxOfTheFlow.BoxDefs
import Mathlib
set_option autoImplicit false
noncomputable section
open MeasureTheory ProbabilityTheory
open scoped Quaternion
namespace YangMills.Construction.BoxGaussian
def sliceGaussianMeasurableStatement : Prop :=
  ∀ Tb : RenormalizationStepParameters.ParameterAssignment, Tb.Admissible → ∀ κ₀ : ℝ, 1 / 27 ≤ κ₀ → κ₀ ≤ 1 / 21 → ∃ xs : ℝ,
    ∀ (x : ℝ) (R k n : ℕ) [NeZero n] (o : TorusFields.TorusSite n), xs ≤ x → R = boxRadius κ₀ x → 16 * R < n →
      ∀ E : Set ((TorusFields.TorusBond n → BlockAverages.imaginaryQuaternions) ×
          (TorusFields.TorusBond n → BlockAverages.imaginaryQuaternions)), MeasurableSet E →
        Measurable fun A : {A : TorusFields.TorusBond n → BlockAverages.imaginaryQuaternions //
            IsAxialSmall o R (boxScale x) A} =>
          sliceGaussian Tb.coupling Tb.side k o R x A.1 {ζ | (A.1, ζ) ∈ E}
end YangMills.Construction.BoxGaussian
end
