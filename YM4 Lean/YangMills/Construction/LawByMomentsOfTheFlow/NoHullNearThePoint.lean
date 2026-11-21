import YangMills.Construction.LawByMomentsOfTheFlow.WindowOfTheLaw
import Mathlib
set_option autoImplicit false
noncomputable section
open MeasureTheory ProbabilityTheory
namespace YangMills.Construction.MomentLaw
open TorusFields WeightedResponses ResponseInTheExpansion
def noLumpNearPointStatement : Prop :=
  ForAllPoints fun Λ C c X₀ S => X₀ ≤ S.scaleCoupling →
    (∀ u, S.lastSeparated ≤ u → u ≤ S.lastSeparated + 2 * S.logIndex + 3 →
      S.law u (S.levelSide u) {w | ¬ Disjoint (S.state u (S.levelSide u) w).2.1
          (supBall (S.originSite u (S.levelSide u)) ((S.range : ℝ) ^ 3))} ≤
        ENNReal.ofReal (C 0 * Real.exp (-(c * S.scaleCoupling)))) ∧
    ∀ (u d n : ℕ) [NeZero n], S.lastSeparated ≤ u → u + d = S.lastSeparated + 2 * S.logIndex + 3 →
      n = S.levelSide (u + d) →
      S.law (u + d) n {w | ¬ S.NoLumpNear u ((S.range : ℝ) ^ 3) d n w} ≤
        ENNReal.ofReal (C 0 * Real.exp (-(c * S.scaleCoupling)))
end YangMills.Construction.MomentLaw
end
