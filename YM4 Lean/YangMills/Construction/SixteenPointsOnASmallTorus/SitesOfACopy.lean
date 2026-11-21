import YangMills.Construction.ResponseInTheExpansion.SeveralSupportsInOneStep
import YangMills.Construction.SixteenPointsOnASmallTorus.SixteenPointsDefs
import Mathlib
set_option autoImplicit false
noncomputable section
open MeasureTheory
namespace YangMills.Construction.SmallTorusCopies
def reflectedWeightSupportStatement : Prop :=
  ∀ (L : ℕ) [NeZero L], Odd L → ∀ (K κ t : ℕ) (ρ H : ℝ) (Λ : NNReal) (f : TestFunctions.EuclideanFourSpace → ℝ), t ≤ κ → 0 < ρ →
    ρ ≤ cellLength L K κ / 4 → IsLocalizedSource (cellLength L K κ) ρ H Λ f →
      3 * levelSpacing L K t ≤ ρ → ∀ k : Fin 4 → Fin 2,
      ((ResponseInTheExpansion.weightSupportSites L t (twoCellSide L κ t)
        (reflectedWeight (levelSpacing L K 0) (L ^ κ) (fun μ => (k μ : ℕ)) f)).card : ℝ) ≤
          81 * (ρ / levelSpacing L K t) ^ 4
end YangMills.Construction.SmallTorusCopies
end
