import YangMills.Construction.LawByMomentsOfTheFlow.WindowOfTheLaw
import Mathlib
set_option autoImplicit false
noncomputable section
open MeasureTheory ProbabilityTheory
namespace YangMills.Construction.MomentLaw
open TorusFields WeightedResponses ResponseInTheExpansion
def curvatureMomentsNearPointStatement : Prop :=
  ForAllPoints fun Λ C _ X₀ S => X₀ ≤ S.scaleCoupling →
    ∀ (u d n : ℕ) [NeZero n], S.lastSeparated ≤ u → u ≤ S.lastSeparated + S.logIndex + 2 →
      u + d = S.lastSeparated + 2 * S.logIndex + 3 → n = S.levelSide (u + d) →
      ∀ p : OrientedPlaquette (fineSide Λ.stepParams.side d n),
        (TorusFields.supDist p.1.1 (S.originSite u (fineSide Λ.stepParams.side d n)) : ℝ) ≤ 4 * (S.range : ℝ) ^ 2 →
      ∀ q : ℕ, 1 ≤ q →
        ∫⁻ w, Set.indicator {w | S.NoLumpNear u ((S.range : ℝ) ^ 3) d n w}
            (fun w => ENNReal.ofReal (curvature (topField Λ.stepParams u (fineSide Λ.stepParams.side d n)
              (sampleBelow Λ.stepParams u d n w)) p.1.1 p.1.2.1 p.1.2.2 ^ (2 * q))) w ∂(S.law (u + d) n) ≤
          ENNReal.ofReal (C q * S.scaleCoupling ^ (-(q : ℝ)))
end YangMills.Construction.MomentLaw
end
