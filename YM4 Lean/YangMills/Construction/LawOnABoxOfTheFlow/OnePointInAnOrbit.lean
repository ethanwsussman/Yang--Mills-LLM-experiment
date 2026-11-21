import YangMills.Construction.ClusterExpansionOfAStep.ParametersOfARenormalizationStep
import YangMills.Construction.LawOnABoxOfTheFlow.BoxDefs
import Mathlib
set_option autoImplicit false
noncomputable section
open MeasureTheory ProbabilityTheory
open scoped Quaternion
namespace YangMills.Construction.BoxGaussian
open TorusFields RenormalizationStepParameters TorusLumps BlockAverages WeightedResponses ResponseInTheExpansion
def chartMeetsOrbitOnceStatement : Prop :=
  ∀ Tb : ParameterAssignment, Tb.Admissible → ∀ κ₀ : ℝ, 1 / 27 ≤ κ₀ → κ₀ ≤ 1 / 21 → ∀ C₀ : ℝ, 0 < C₀ → ∃ xs : ℝ,
    ∀ (x : ℝ) (R k n : ℕ) [NeZero n] (o : TorusSite n) (A : TorusBond n → imaginaryQuaternions),
      xs ≤ x → R = boxRadius κ₀ x → 16 * R < n → IsAxialSmall o R (boxScale x) A →
      ∀ (W : TorusField n) (γ : TorusSite n → UnitQuaternion) (ζ ζ' : TorusBond n → imaginaryQuaternions),
        IsSupportedGauge o R γ →
        ζ ∈ sliceEllipsoid Tb.coupling Tb.side k o R A (C₀ * (R : ℝ) ^ 4 * boxScale x ^ 2) →
        ζ' ∈ sliceEllipsoid Tb.coupling Tb.side k o R A (C₀ * (R : ℝ) ^ 4 * boxScale x ^ 2) →
        IsInChart (supBall o (2 * R)) A ζ W → IsInChart (supBall o (2 * R)) A ζ' (gaugeTransform γ W) →
        ζ' = ζ ∧ ∀ z, γ z = 1
end YangMills.Construction.BoxGaussian
end
