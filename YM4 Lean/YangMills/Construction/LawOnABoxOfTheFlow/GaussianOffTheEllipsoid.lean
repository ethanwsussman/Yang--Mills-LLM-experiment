import YangMills.Construction.ClusterExpansionOfAStep.ParametersOfARenormalizationStep
import YangMills.Construction.LawOnABoxOfTheFlow.BoxDefs
import Mathlib
set_option autoImplicit false
noncomputable section
open MeasureTheory ProbabilityTheory
open scoped Quaternion
namespace YangMills.Construction.BoxGaussian
open TorusFields RenormalizationStepParameters TorusLumps BlockAverages WeightedResponses ResponseInTheExpansion
def gaussianTailOffEllipsoidStatement : Prop :=
  ∀ Tb : ParameterAssignment, Tb.Admissible → ∀ κ₀ : ℝ, 1 / 27 ≤ κ₀ → κ₀ ≤ 1 / 21 → ∀ C₀ : ℝ, 0 < C₀ → ∃ xs : ℝ,
    ∀ (x : ℝ) (R k n : ℕ) [NeZero n] (o : TorusSite n) (A : TorusBond n → imaginaryQuaternions),
      xs ≤ x → R = boxRadius κ₀ x → 16 * R < n → IsAxialSmall o R (boxScale x) A →
      2 * hessianForm Tb.coupling Tb.side k (supBall o (2 * R)) A A ≤ C₀ * (R : ℝ) ^ 4 * boxScale x ^ 2 →
      IsProbabilityMeasure (sliceGaussian Tb.coupling Tb.side k o R x A) ∧
      (sliceGaussian Tb.coupling Tb.side k o R x A).real
          (sliceEllipsoid Tb.coupling Tb.side k o R A (C₀ * (R : ℝ) ^ 4 * boxScale x ^ 2))ᶜ ≤ Real.exp (-((R : ℝ) ^ 4))
end YangMills.Construction.BoxGaussian
end
