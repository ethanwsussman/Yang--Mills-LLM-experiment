import YangMills.Construction.SixteenPointsOnASmallTorus.SixteenPointsDefs
import Mathlib
set_option autoImplicit false
noncomputable section
open MeasureTheory
namespace YangMills.Construction.SmallTorusCopies
def levelsBelowRadiusStatement : Prop :=
  ResponseInTheExpansion.HoldsOnParameterFamilies fun Tb y => ∀ (Ξ β : ℝ) (K κ : ℕ) (ρ : ℝ), IsAdmissibleFlow (Tb.stepParameters y) Ξ β K → 2 ≤ κ → 0 < ρ →
    ρ ≤ cellLength Tb.side K κ / 4 → ∀ s : ℕ, radiusLevel (Tb.stepParameters y) β K ρ = some s →
      s ≤ K ∧ ∀ t ≤ s, FitsAtLevel (Tb.stepParameters y) β K ρ t ∧ t < κ ∧
        2 ^ 13 * rangeAtLevel (Tb.stepParameters y) β t ≤ (Tb.side : ℝ) ^ (κ - t) ∧
          TorusLumps.IsBlockTorusSide (Tb.stepParameters y) (twoCellSide Tb.side κ t)
end YangMills.Construction.SmallTorusCopies
end
