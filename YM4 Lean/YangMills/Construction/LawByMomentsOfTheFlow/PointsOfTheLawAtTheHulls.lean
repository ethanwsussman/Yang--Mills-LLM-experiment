import YangMills.Construction.HullsInEveryVolume.HullDefs
import YangMills.Construction.LawByMomentsOfTheFlow.PointOfTheLaw
import Mathlib
set_option autoImplicit false
noncomputable section
open MeasureTheory
namespace YangMills.Construction.MomentLaw
def momentPointsExistStatement : Prop :=
  HullTrees.EventuallyInParameters fun Tb Kr y =>
    ∀ g : ℝ, 0 < g → y ≤ (g ^ 2)⁻¹ → ∀ (k : ℕ) [NeZero k], 2 ≤ k → k ≤ 8 → ∀ R d : ℝ, 0 < d →
      ∀ (P : LevelTestFunctions.LevelData k) (β : ℝ),
        P.SupAdmissible (Tb.stepParameters y).side R d →
        (Tb.stepParameters y).side * (Tb.stepParameters y).n₀ ≤ P.period (Tb.stepParameters y).side →
        WeightedResponses.couplingWindowTop (Tb.stepParameters y) g ≤ β →
        WeightedResponses.IsFirstPassage (Tb.stepParameters y)
          (WeightedResponses.couplingWindowTop (Tb.stepParameters y) g) β P.windowLevel →
        ∃ S : MomentPoint ⟨Tb, Kr, y, g, k, R, d⟩, S.data = P ∧ S.β = β
end YangMills.Construction.MomentLaw
end
