import YangMills.Construction.SixteenPointsOnASmallTorus.SixteenPointsDefs
import Mathlib
set_option autoImplicit false
noncomputable section
open MeasureTheory
namespace YangMills.Construction.SmallTorusCopies
def reflectedWeightNormBoundStatement : Prop :=
  ∀ (L : ℕ) [NeZero L], Odd L → ∀ (K κ t : ℕ) (ρ H : ℝ) (Λ : NNReal)
    (f : TestFunctions.EuclideanFourSpace → ℝ), t ≤ κ → 0 < ρ →
    ρ ≤ cellLength L K κ / 4 → IsLocalizedSource (cellLength L K κ) ρ H Λ f →
      levelSpacing L K t ≤ min 1 ρ → ∀ k : Fin 4 → Fin 2,
      WeightedResponses.weightNorm L t (m := WeightedResponses.fineSide L t (twoCellSide L κ t))
        (reflectedWeight (levelSpacing L K 0) (L ^ κ) (fun μ => (k μ : ℕ)) f) ≤ 2 * sourceNorm ρ H Λ
end YangMills.Construction.SmallTorusCopies
end
