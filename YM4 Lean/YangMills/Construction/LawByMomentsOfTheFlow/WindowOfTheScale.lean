import YangMills.Construction.LawByMomentsOfTheFlow.PointOfTheLaw
import Mathlib
set_option autoImplicit false
noncomputable section
open MeasureTheory ProbabilityTheory
namespace YangMills.Construction.MomentLaw
open WeightedResponses
def scaleWindowStatement : Prop :=
  ForAllPoints fun Λ C _ X₀ S => X₀ ≤ S.scaleCoupling →
    (Λ.stepParams.side : ℝ) ^ (-(S.logIndex : ℝ) / 4) ≤ S.scaleCoupling⁻¹ ∧ (2 : ℝ) ^ (-(S.logIndex : ℝ)) ≤ S.scaleCoupling ^ (-(1 / 2) : ℝ) ∧ 3 ≤ S.logIndex ∧
    (S.scaleCoupling - couplingWindowTop Λ.stepParams Λ.g) / (2 * Λ.stepParams.B) ≤ (S.data.windowLevel : ℝ) - (S.data.scaleLevel : ℝ) ∧
    4 * (S.logIndex : ℝ) ≤ (S.scaleCoupling - couplingWindowTop Λ.stepParams Λ.g) / (2 * Λ.stepParams.B) ∧ S.lastSeparated + 2 * S.logIndex + 3 ≤ S.data.windowLevel ∧
    ∀ u, S.lastSeparated ≤ u → u ≤ S.lastSeparated + 2 * S.logIndex + 3 → |S.coupling u - S.scaleCoupling| ≤ C 0 * Real.log S.scaleCoupling ∧ Λ.stepParams.side ^ S.logIndex ≤ S.levelSide u
end YangMills.Construction.MomentLaw
end
