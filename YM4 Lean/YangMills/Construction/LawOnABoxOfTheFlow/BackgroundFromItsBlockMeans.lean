import YangMills.Construction.LawOnABoxOfTheFlow.EventsOfABox
import Mathlib
set_option autoImplicit false
noncomputable section
open MeasureTheory ProbabilityTheory
open scoped Quaternion
namespace YangMills.Construction.BoxGaussian
open YangMills.Construction.TorusFields YangMills.Construction.TorusLumps YangMills.Construction.RenormalizationStepParameters
open YangMills.Construction.WeightedResponses YangMills.Construction.ResponseInTheExpansion
open YangMills.Construction.BlockAverages YangMills.Construction.BoxEvents
def backgroundFromBlockMeansStatement : Prop :=
  ∀ (L : ℕ) [NeZero L], Odd L → 3 ≤ L → ∀ C₂ : ℝ, ∃ (C : ℝ) (R₀ : ℕ),
    ∀ (s n R : ℕ) [NeZero n] (o : TorusSite (fineSide L s n)) (δ : ℝ)
      (F : TorusPlaquette (fineSide L s n) → imaginaryQuaternions),
      R₀ ≤ R → s = coarseningSteps L R → 16 * R < fineSide L s n → 0 ≤ δ →
      (∀ (l : List (Fin 4)), l.length = 2 → ∀ p ∈ plaquettesIn (supBall o ((R : ℝ) / 4)),
        ‖iteratedDiff l F p‖ ≤ C₂ * ((R : ℝ) ^ 2)⁻¹ * δ) →
      (∀ P ∈ plaquettesIn (Finset.univ : Finset (TorusSite n)),
        (L : ℝ) ^ s * supDist P.1 (siteAbove L s n o) ≤ (R : ℝ) / 8 + 2 * (L : ℝ) ^ s →
        ‖∑ p ∈ plaquettesIn (Finset.univ : Finset (TorusSite (fineSide L s n))), blockWeight L s P p • F p‖ ≤
          13 * (L : ℝ) ^ s * δ) →
      ∀ p ∈ plaquettesIn (supBall o ((R : ℝ) / 8)), ‖F p‖ ≤ C * (R : ℝ) ^ (-(2 / 3 : ℝ)) * δ
end YangMills.Construction.BoxGaussian
end
