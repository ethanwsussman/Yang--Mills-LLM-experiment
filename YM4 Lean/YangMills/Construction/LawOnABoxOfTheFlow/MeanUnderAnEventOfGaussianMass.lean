import YangMills.Construction.ClusterExpansionOfAStep.ParametersOfARenormalizationStep
import YangMills.Construction.LawOnABoxOfTheFlow.BoxDefs
import Mathlib
set_option autoImplicit false
noncomputable section
open MeasureTheory ProbabilityTheory
open scoped Quaternion
namespace YangMills.Construction.BoxGaussian
open TorusFields RenormalizationStepParameters BlockAverages ResponseInTheExpansion
def criticalCurlBoundFromLargeEventStatement : Prop :=
  ∀ Tb : ParameterAssignment, Tb.Admissible → ∀ κ₀ : ℝ, 1 / 27 ≤ κ₀ → κ₀ ≤ 1 / 21 → ∃ K xs : ℝ,
    ∀ (x : ℝ) (R k n : ℕ) [NeZero n] (o : TorusSite n) (A B : TorusBond n → imaginaryQuaternions),
      xs ≤ x → R = boxRadius κ₀ x → 16 * R < n →
      IsAxialSmall o R (boxScale x) A → B - A ∈ gaugeSlice o R A →
      (∀ η : TorusBond n → imaginaryQuaternions, (∀ b, b ∉ bondsTouching o R → η b = 0) →
        hessianForm Tb.coupling Tb.side k (supBall o (2 * R)) B η = 0) →
      ∀ (E : Set (TorusBond n → imaginaryQuaternions)) (w : TorusPlaquette n → ℝ) (b : ℝ), MeasurableSet E →
        (∑ p ∈ plaquettesIn (supBall o (2 * R)), w p ^ 2 ≤ 1) →
        (0.6 : ℝ) ≤ (sliceGaussian Tb.coupling Tb.side k o R x A).real E →
        (∀ ζ ∈ E, ‖∑ p ∈ plaquettesIn (supBall o (2 * R)), w p • lieFormCurl (A + ζ) p‖ ≤ b) →
        ‖∑ p ∈ plaquettesIn (supBall o (2 * R)), w p • lieFormCurl B p‖ ≤ b + K * x ^ (-(1 / 2 : ℝ))
end YangMills.Construction.BoxGaussian
end
