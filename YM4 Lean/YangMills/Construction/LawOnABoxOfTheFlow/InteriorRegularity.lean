import YangMills.Construction.LawOnABoxOfTheFlow.BoxDefs
import YangMills.Construction.ResponseInTheExpansion.PairsAtALevel
import Mathlib
set_option autoImplicit false
noncomputable section
open MeasureTheory ProbabilityTheory
open scoped Quaternion
namespace YangMills.Construction.BoxGaussian
open TorusFields RenormalizationStepParameters TorusLumps BlockAverages WeightedResponses ResponseInTheExpansion
def interiorRegularityStatement : Prop :=
  HoldsAtAdmissibleParameters fun Tb _ => ∀ Cp c : ℝ, 0 < c → ∀ j : ℕ, ∃ (C c' : ℝ) (R₀ : ℕ), 0 < c' ∧
    ∀ (k n : ℕ) [NeZero n] (o : TorusSite n) (R : ℕ) (A : TorusBond n → imaginaryQuaternions), R₀ ≤ R → 16 * R < n →
      (∀ b ∈ bondsWithin (supBall o (2 * R)), ‖A b‖ ≤ (R : ℝ) ^ Cp) →
      (∀ η : TorusBond n → imaginaryQuaternions, (∀ b, b ∉ bondsTouching o R → η b = 0) →
        |hessianForm Tb.coupling Tb.side k (supBall o (2 * R)) A η| ≤ Real.exp (-(c * R)) * ∑ b : TorusBond n, ‖η b‖) →
      ∀ (l : List (Fin 4)), l.length = j → ∀ p ∈ plaquettesIn (supBall o ((R : ℝ) / 4)),
        ‖iteratedDiff l (lieFormCurl A) p‖ ≤
          C * ((R : ℝ) ^ j)⁻¹ *
              Real.sqrt (((R : ℝ) ^ 4)⁻¹ * curlNormSq (supBall o R) A) + Real.exp (-(c' * R))
end YangMills.Construction.BoxGaussian
end
