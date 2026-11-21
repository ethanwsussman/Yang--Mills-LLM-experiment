import YangMills.Construction.ClusterExpansionOfAStep.ParametersOfARenormalizationStep
import YangMills.Construction.LawOnABoxOfTheFlow.BoxDefs
import Mathlib
set_option autoImplicit false
noncomputable section
open MeasureTheory ProbabilityTheory
open scoped Quaternion
namespace YangMills.Construction.BoxGaussian
def coldFieldsInChartStatement : Prop :=
  ∀ Tb : RenormalizationStepParameters.ParameterAssignment, Tb.Admissible → ∀ κ₀ : ℝ, 1 / 27 ≤ κ₀ → κ₀ ≤ 1 / 21 →
    ∃ C₀ xs : ℝ, 0 < C₀ ∧
    ∀ (x : ℝ) (R k n : ℕ) [NeZero n] (o : TorusFields.TorusSite n)
      (A : TorusFields.TorusBond n → BlockAverages.imaginaryQuaternions),
      xs ≤ x → R = boxRadius κ₀ x → 16 * R < n → IsAxialSmall o R (boxScale x) A →
      ∀ W : TorusFields.TorusField n,
        (∀ p ∈ TorusFields.plaquettesIn (ResponseInTheExpansion.supBall o (2 * R)),
          TorusFields.curvature W p.1 p.2.1 p.2.2 ≤ boxScale x) →
        (∀ b ∈ bondsWithin (ResponseInTheExpansion.supBall o (2 * R)), b ∉ bondsTouching o R →
          W b.1 b.2 = BlockAverages.expUnit (A b)) →
        ∃ (γ : TorusFields.TorusSite n → BlockAverages.UnitQuaternion)
          (ζ : TorusFields.TorusBond n → BlockAverages.imaginaryQuaternions),
          IsSupportedGauge o R γ ∧
          ζ ∈ sliceEllipsoid Tb.coupling Tb.side k o R A (C₀ * (R : ℝ) ^ 4 * boxScale x ^ 2) ∧
          IsInChart (ResponseInTheExpansion.supBall o (2 * R)) A ζ (TorusFields.gaugeTransform γ W)
end YangMills.Construction.BoxGaussian
end
