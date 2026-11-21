import YangMills.Construction.LawByMomentsOfTheFlow.WindowOfTheLaw
import Mathlib
set_option autoImplicit false
noncomputable section
namespace YangMills.Construction.MomentLaw
open TorusFields TorusLumps WeightedResponses
def supportTotalNearQuadraticStatement : Prop :=
  ForAllPoints fun Λ C c X₀ S => X₀ ≤ S.scaleCoupling →
    ∀ (i : Fin Λ.k) (q : StageState S.tower S.lastSeparated (S.levelSide S.lastSeparated)),
    IsLiveState Λ.stepParams (S.tower.stage S.lastSeparated).coupling (S.tower.stage S.lastSeparated).labelWeight
      q.1 q.2.1 q.2.2 →
    S.IsGoodConfig S.lastSeparated (S.levelSide S.lastSeparated) q.1 q.2.1 →
    |S.supportTotal S.lastSeparated (S.levelSide S.lastSeparated) i q -
        1 / 2 * colourEval (S.supportForm S.lastSeparated (S.levelSide S.lastSeparated) i)
          (S.cutoffColourForm S.lastSeparated (S.levelSide S.lastSeparated) q.1)
          (S.cutoffColourForm S.lastSeparated (S.levelSide S.lastSeparated) q.1)| ≤
      C 0 * ((S.range : ℝ) ^ 7 * S.localCurvature S.lastSeparated (S.levelSide S.lastSeparated) q.1 ^ 3 +
        (S.range : ℝ) ^ 4 * S.scaleCoupling ^ (-(1 / 2) : ℝ) *
          S.localCurvature S.lastSeparated (S.levelSide S.lastSeparated) q.1 ^ 2 +
        (S.range : ℝ) ^ 4 * Real.exp (-(c * (S.range : ℝ) ^ 2)) *
          S.meanScore S.lastSeparated (S.levelSide S.lastSeparated) i q) ∧
    |colourEval (S.supportForm S.lastSeparated (S.levelSide S.lastSeparated) i)
        (S.cutoffColourForm S.lastSeparated (S.levelSide S.lastSeparated) q.1)
        (S.cutoffColourForm S.lastSeparated (S.levelSide S.lastSeparated) q.1)| ≤
      C 0 * (S.range : ℝ) ^ 4 * S.localCurvature S.lastSeparated (S.levelSide S.lastSeparated) q.1 ^ 2
end YangMills.Construction.MomentLaw
end
