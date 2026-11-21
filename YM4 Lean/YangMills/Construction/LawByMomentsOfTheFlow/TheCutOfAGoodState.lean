import YangMills.Construction.LawByMomentsOfTheFlow.WindowOfTheLaw
import Mathlib
set_option autoImplicit false
noncomputable section
open MeasureTheory ProbabilityTheory
namespace YangMills.Construction.MomentLaw
open TorusFields WeightedResponses ResponseInTheExpansion BlockAverages
def goodConfigCutoffStatement : Prop :=
  ForAllPoints fun Λ _ _ X₀ S => X₀ ≤ S.scaleCoupling → ∀ u, S.lastSeparated ≤ u →
    u ≤ S.lastSeparated + 2 * S.logIndex + 3 → ∀ (n : ℕ) [NeZero n], n = S.levelSide u →
    ∀ (W : TorusField n) (Y : Finset (TorusSite n)), S.IsGoodConfig u n W Y →
    (∀ c : TorusBond n, c.1 ∈ supBall (S.originSite u n) (2 * S.rangeSq) →
      c.1 + TorusFields.unitStep n c.2 ∈ supBall (S.originSite u n) (2 * S.rangeSq) →
      ‖(axialCoords Λ.stepParams W (S.originSite u n) c : Quaternion ℝ)‖ ≤
        4 * ((TorusFields.supDist c.1 (S.originSite u n) : ℝ) + 1) * S.localCurvature u n W) ∧
    (∀ p : OrientedPlaquette n, curlNorm (S.cutoffColourForm u n W) p.1 ≤ 60 * S.localCurvature u n W) ∧
    (∀ v : ℝ, 0 ≤ v → v ≤ 1 → ∀ (x : TorusSite n) (μ ν : Fin 4), μ < ν →
      curvature (expField v (S.cutoffLie u n W)) x μ ν ≤ 64 * S.localCurvature u n W) ∧
    ∃ g : TorusSite n → UnitQuaternion, ∀ c : TorusBond n, c.1 ∈ supBall (S.originSite u n) S.rangeSq →
      c.1 + TorusFields.unitStep n c.2 ∈ supBall (S.originSite u n) S.rangeSq →
      S.smoothedField u n W c.1 c.2 = gaugeTransform g W c
end YangMills.Construction.MomentLaw
end
