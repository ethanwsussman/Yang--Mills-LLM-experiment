import YangMills.Construction.ClusterExpansionOfAStep.ParametersOfARenormalizationStep
import YangMills.Construction.LawOnABoxOfTheFlow.BoxDefs
import Mathlib
set_option autoImplicit false
noncomputable section
open MeasureTheory ProbabilityTheory
open scoped Quaternion
namespace YangMills.Construction.BoxGaussian
def borelBackgroundStatement : Prop :=
  ∀ Tb : RenormalizationStepParameters.ParameterAssignment, Tb.Admissible → ∀ κ₀ : ℝ, 1 / 27 ≤ κ₀ → κ₀ ≤ 1 / 21 → ∃ C xs : ℝ,
    ∀ (x : ℝ) (R k n : ℕ) [NeZero n] (o : TorusFields.TorusSite n), xs ≤ x → R = boxRadius κ₀ x → 16 * R < n →
      ∃ Bf : (TorusFields.TorusBond n → BlockAverages.imaginaryQuaternions) →
          TorusFields.TorusBond n → BlockAverages.imaginaryQuaternions, Measurable Bf ∧
        ∀ A : TorusFields.TorusBond n → BlockAverages.imaginaryQuaternions, IsAxialSmall o R (boxScale x) A →
          Bf A - A ∈ gaugeSlice o R A ∧
          (∀ η : TorusFields.TorusBond n → BlockAverages.imaginaryQuaternions, (∀ b, b ∉ bondsTouching o R → η b = 0) →
            hessianForm Tb.coupling Tb.side k (ResponseInTheExpansion.supBall o (2 * R)) (Bf A) η = 0) ∧
          curlNormSq (ResponseInTheExpansion.supBall o (2 * R)) (Bf A) ≤ C * (R : ℝ) ^ 4 * boxScale x ^ 2 ∧
          (∀ b ∈ bondsWithin (ResponseInTheExpansion.supBall o (2 * R)), ‖Bf A b‖ ≤ C * (R : ℝ) ^ 3 * boxScale x) ∧
          ∀ u : TorusFields.TorusPlaquette n → Fin 3 → ℝ,
            (sliceGaussian Tb.coupling Tb.side k o R x A).map
                (fun ζ => colourPairing (ResponseInTheExpansion.supBall o (2 * R)) u fun p =>
                  ResponseInTheExpansion.lieFormCurl (A + ζ) p - ResponseInTheExpansion.lieFormCurl (Bf A) p) =
              gaussianReal 0 (x⁻¹ * curlQuadForm Tb.coupling Tb.side k o R u).toNNReal
end YangMills.Construction.BoxGaussian
end
