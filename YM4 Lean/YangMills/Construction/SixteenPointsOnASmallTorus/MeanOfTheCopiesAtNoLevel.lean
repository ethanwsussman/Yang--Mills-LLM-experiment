import YangMills.Construction.Lattice.SettingOfTheTorusBound
import YangMills.Construction.SixteenPointsOnASmallTorus.SixteenPointsDefs
import Mathlib
set_option autoImplicit false
noncomputable section
open MeasureTheory
namespace YangMills.Construction.SmallTorusCopies
def reflectedMeanWithoutLevelStatement : Prop :=
  ResponseInTheExpansion.HoldsOnParameterFamilies fun Tb y => ∀ Ξ : ℝ, y + 2 * Tb.B ≤ Ξ → ∃ C : ℝ, 0 ≤ C ∧
    ∀ (β : ℝ) (K κ : ℕ) (ρ H : ℝ) (Λ : NNReal) (f : TestFunctions.EuclideanFourSpace → ℝ),
    IsAdmissibleFlow (Tb.stepParameters y) Ξ β K → 2 ≤ κ → 0 < ρ → ρ ≤ cellLength Tb.side K κ / 4 →
    IsLocalizedSource (cellLength Tb.side K κ) ρ H Λ f → radiusLevel (Tb.stepParameters y) β K ρ = none →
    ∀ z : TorusFields.TorusSite (2 * Tb.side ^ κ),
      reflectedProductMean β (levelSpacing Tb.side K 0) (Tb.side ^ κ) 2 z f 0 ≤
        (C * (1 + TorusBound.logPos (1 / ρ)) ^ ((1 : ℝ) / 25) * H) ^ 16
end YangMills.Construction.SmallTorusCopies
end
