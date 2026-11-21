import YangMills.Construction.SixteenPointsOnASmallTorus.SixteenPointsDefs
import Mathlib
set_option autoImplicit false
noncomputable section
open MeasureTheory
namespace YangMills.Construction.SmallTorusCopies
def reflectedMeanNonnegStatement : Prop :=
  ∀ ℓ : TorusLumps.StepParameters, ℓ.Admissible → ∀ (β : ℝ) (K κ : ℕ) (ρ H : ℝ) (Λ : NNReal)
    (f : TestFunctions.EuclideanFourSpace → ℝ) (e : ℝ) (z : TorusFields.TorusSite (2 * ℓ.side ^ κ)),
    0 < β → 0 < K → 2 ≤ κ → 0 < ρ → ρ ≤ cellLength ℓ.side K κ / 4 → IsLocalizedSource (cellLength ℓ.side K κ) ρ H Λ f →
      0 ≤ reflectedProductMean β (levelSpacing ℓ.side K 0) (ℓ.side ^ κ) 2 z f e
end YangMills.Construction.SmallTorusCopies
end
