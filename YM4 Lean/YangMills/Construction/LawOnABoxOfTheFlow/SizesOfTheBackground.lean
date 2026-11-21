import YangMills.Construction.LawOnABoxOfTheFlow.BoxDefs
import YangMills.Construction.ResponseInTheExpansion.PairsAtALevel
import Mathlib
set_option autoImplicit false
noncomputable section
open MeasureTheory ProbabilityTheory
open scoped Quaternion
namespace YangMills.Construction.BoxGaussian
open TorusFields TorusLumps WeightedResponses ResponseInTheExpansion RenormalizationStepParameters BlockAverages
variable {n : ℕ} [NeZero n]
open Classical in
def restrictedCurl (S : Finset (TorusSite n)) (B : TorusBond n → imaginaryQuaternions) (p : TorusPlaquette n) :
    imaginaryQuaternions :=
  if p ∈ plaquettesIn S then lieFormCurl B p else 0
def backgroundCurlBoundsStatement : Prop :=
  HoldsAtAdmissibleParameters fun Tb _ => ∀ κ₀ : ℝ, 1 / 27 ≤ κ₀ → κ₀ ≤ 1 / 21 → ∀ C₃ : ℝ, 0 ≤ C₃ →
    ∃ (C xs : ℝ) (Cj : ℕ → ℝ),
    ∀ (x : ℝ) (R k n : ℕ) [NeZero n] (o : TorusSite n) (B : TorusBond n → imaginaryQuaternions),
      xs ≤ x → R = boxRadius κ₀ x → 16 * R < n →
      curlNormSq (supBall o (2 * R)) B ≤ C₃ * (R : ℝ) ^ 4 * boxScale x ^ 2 →
      (∀ b ∈ bondsWithin (supBall o (2 * R)), ‖B b‖ ≤ C₃ * (R : ℝ) ^ 3 * boxScale x) →
      (∀ η : TorusBond n → imaginaryQuaternions, (∀ b, b ∉ bondsTouching o R → η b = 0) →
        hessianForm Tb.coupling Tb.side k (supBall o (2 * R)) B η = 0) →
      (∀ p ∈ plaquettesIn (supBall o (2 * R)), ‖lieFormCurl B p‖ ≤ C * (R : ℝ) ^ 2 * boxScale x) ∧
      ∀ (l : List (Fin 4)), ∀ p ∈ plaquettesIn (supBall o ((R : ℝ) / 4)),
        ‖iteratedDiff l (restrictedCurl (supBall o (2 * R)) B) p‖ ≤
          Cj l.length * ((R : ℝ) ^ l.length)⁻¹ * boxScale x
end YangMills.Construction.BoxGaussian
end
