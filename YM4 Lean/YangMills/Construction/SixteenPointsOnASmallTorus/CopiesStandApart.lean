import YangMills.Construction.ResponseInTheExpansion.SeveralSupportsInOneStep
import YangMills.Construction.SixteenPointsOnASmallTorus.SixteenPointsDefs
import Mathlib
set_option autoImplicit false
noncomputable section
open MeasureTheory
namespace YangMills.Construction.SmallTorusCopies
def reflectedSupportsSeparatedStatement : Prop :=
  ∀ (L : ℕ) [NeZero L], Odd L → ∀ (K κ t : ℕ) (ρ H : ℝ) (Λ : NNReal) (f : TestFunctions.EuclideanFourSpace → ℝ),
    t ≤ κ → 0 < ρ → ρ ≤ cellLength L K κ / 4 → IsLocalizedSource (cellLength L K κ) ρ H Λ f →
      ∀ k k' : Fin 4 → Fin 2, k ≠ k' →
      ∀ Y ∈ TorusLumps.thickening 2 (ResponseInTheExpansion.weightSupportSites L t (twoCellSide L κ t)
          (reflectedWeight (levelSpacing L K 0) (L ^ κ) (fun μ => (k μ : ℕ)) f)),
      ∀ Y' ∈ TorusLumps.thickening 2 (ResponseInTheExpansion.weightSupportSites L t (twoCellSide L κ t)
          (reflectedWeight (levelSpacing L K 0) (L ^ κ) (fun μ => (k' μ : ℕ)) f)),
        2 * (ρ / levelSpacing L K t) - 6 ≤ (TorusFields.supDist Y Y' : ℝ)
end YangMills.Construction.SmallTorusCopies
end
