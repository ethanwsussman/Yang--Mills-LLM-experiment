import YangMills.Construction.LawOnABoxOfTheFlow.BoxDefs
import Mathlib
set_option autoImplicit false
noncomputable section
open MeasureTheory ProbabilityTheory
open scoped Quaternion
namespace YangMills.Construction
namespace BoxGaussian
def covariantGradientGapStatement : Prop :=
  ∀ (n : ℕ) [NeZero n] (o : TorusFields.TorusSite n) (R : ℕ), 1 ≤ R → 8 * R < n →
    ∀ A : TorusFields.TorusBond n → BlockAverages.imaginaryQuaternions,
    (∀ χ : TorusFields.TorusSite n → BlockAverages.imaginaryQuaternions,
      (∀ z, z ∉ ResponseInTheExpansion.supBall o R → χ z = 0) →
      4 * ((R : ℝ) + 1)⁻¹ ^ 2 * ∑ z : TorusFields.TorusSite n, ‖χ z‖ ^ 2 ≤
        ∑ b : TorusFields.TorusBond n, ‖covariantGrad A χ b‖ ^ 2) ∧
    ∀ (χ : TorusFields.TorusSite n → BlockAverages.imaginaryQuaternions) (z : TorusFields.TorusSite n)
      (X : BlockAverages.imaginaryQuaternions),
      (∀ z', z' ∉ ResponseInTheExpansion.supBall o R → χ z' = 0) → z ∈ ResponseInTheExpansion.supBall o R →
      (∀ ψ : TorusFields.TorusSite n → BlockAverages.imaginaryQuaternions,
        (∀ z', z' ∉ ResponseInTheExpansion.supBall o R → ψ z' = 0) →
        ∑ b : TorusFields.TorusBond n, inner ℝ (covariantGrad A χ b) (covariantGrad A ψ b) =
          inner ℝ X (ψ z)) →
      ∀ z', ‖χ z'‖ ≤ ‖X‖
end BoxGaussian
end YangMills.Construction
end
