import YangMills.Construction.ClusterExpansionOfAStep.ParametersOfARenormalizationStep
import YangMills.Construction.LawOnABoxOfTheFlow.BoxDefs
import Mathlib
set_option autoImplicit false
noncomputable section
open MeasureTheory ProbabilityTheory
open scoped Quaternion
namespace YangMills.Construction
namespace BoxGaussian
open YangMills.Construction.TorusFields YangMills.Construction.TorusLumps YangMills.Construction.RenormalizationStepParameters
open YangMills.Construction.WeightedResponses YangMills.Construction.ResponseInTheExpansion
open YangMills.Construction.BlockAverages
def ellipsoidBoundsStatement : Prop :=
  ∀ Tb : ParameterAssignment, Tb.Admissible → ∀ κ₀ : ℝ, 1 / 27 ≤ κ₀ → κ₀ ≤ 1 / 21 → ∀ C₀ : ℝ, 0 < C₀ →
    ∃ K xs : ℝ, 1 ≤ K ∧
    ∀ (x : ℝ) (R k n : ℕ) [NeZero n] (o : TorusSite n) (A : TorusBond n → imaginaryQuaternions),
      xs ≤ x → R = boxRadius κ₀ x → 16 * R < n → IsAxialSmall o R (boxScale x) A →
      (∀ ζ ∈ gaugeSlice o R A, 2 * Tb.coercivity * ((R : ℝ) ^ 2)⁻¹ * bondNormSq (supBall o (2 * R)) ζ ≤
        hessianForm Tb.coupling Tb.side k (supBall o (2 * R)) ζ ζ) ∧
      ∀ ζ ∈ sliceEllipsoid Tb.coupling Tb.side k o R A (C₀ * (R : ℝ) ^ 4 * boxScale x ^ 2),
        bondNormSq (supBall o (2 * R)) ζ ≤ K * (R : ℝ) ^ 6 * boxScale x ^ 2 ∧
        (∀ b, ‖ζ b‖ ≤ K * (R : ℝ) ^ 3 * boxScale x) ∧
        curlNormSq (supBall o (2 * R)) (A + ζ) ≤ K * (R : ℝ) ^ 4 * boxScale x ^ 2 ∧
        ∀ W : TorusField n, IsInChart (supBall o (2 * R)) A ζ W →
          ∃ v β : TorusBond n → imaginaryQuaternions,
          (∀ b ∈ bondsWithin (supBall o (2 * R)), W b.1 b.2 = expUnit (v b) ∧ v b = A b + ζ b + β b ∧
            ‖β b‖ ≤ 2 * (‖A b‖ ^ 2 + ‖ζ b‖ ^ 2) ∧ ‖v b‖ ≤ K * (R : ℝ) ^ 3 * boxScale x) ∧
          bondNormSq (supBall o (2 * R)) v ≤ K * (R : ℝ) ^ 6 * boxScale x ^ 2 ∧
          bondNormSq (supBall o (2 * R)) β ≤ K * (R : ℝ) ^ 12 * boxScale x ^ 4 ∧
          ∀ p ∈ plaquettesIn (supBall o (2 * R)), curvature W p.1 p.2.1 p.2.2 ≤ K * (R : ℝ) ^ 2 * boxScale x
end BoxGaussian
end YangMills.Construction
end
