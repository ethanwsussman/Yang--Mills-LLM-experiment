import YangMills.Construction.SixteenPointsOnASmallTorus.SixteenPointsDefs
import Mathlib
set_option autoImplicit false
noncomputable section
open MeasureTheory
namespace YangMills.Construction.SmallTorusCopies
def reflectedMeanTranslationStatement : Prop :=
  ∀ (β a₀ : ℝ) (M c : ℕ) [NeZero M] [NeZero c] (z : TorusFields.TorusSite (c * M))
    (f : TestFunctions.EuclideanFourSpace → ℝ) (e : ℝ),
    reflectedProductMean β a₀ M c z f e = reflectedProductMean β a₀ M c 0 f e
end YangMills.Construction.SmallTorusCopies
end
