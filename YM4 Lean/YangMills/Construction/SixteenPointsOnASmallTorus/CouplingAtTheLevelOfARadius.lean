import YangMills.Construction.Lattice.SettingOfTheTorusBound
import YangMills.Construction.SixteenPointsOnASmallTorus.SixteenPointsDefs
import Mathlib
set_option autoImplicit false
noncomputable section
open MeasureTheory
namespace YangMills.Construction.SmallTorusCopies
def couplingAtRadiusLevelStatement : Prop :=
  ResponseInTheExpansion.HoldsOnParameterFamilies fun Tb y => ∀ Ξ : ℝ, y + 2 * Tb.B ≤ Ξ → ∃ C : ℝ, 0 ≤ C ∧
    ∀ (β : ℝ) (K : ℕ) (ρ : ℝ),
    IsAdmissibleFlow (Tb.stepParameters y) Ξ β K → 0 < ρ →
      (∀ s : ℕ, radiusLevel (Tb.stepParameters y) β K ρ = some s →
        (TorusLumps.couplingFlow (Tb.stepParameters y) β s).1 ≤ C * (1 + TorusBound.logPos (1 / ρ))) ∧
      (radiusLevel (Tb.stepParameters y) β K ρ = none → β ≤ C * (1 + TorusBound.logPos (1 / ρ)))
end YangMills.Construction.SmallTorusCopies
end
