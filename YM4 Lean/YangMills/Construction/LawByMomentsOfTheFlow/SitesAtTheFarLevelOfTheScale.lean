import YangMills.Construction.LawByMomentsOfTheFlow.PointOfTheLaw
import Mathlib
set_option autoImplicit false
noncomputable section
open MeasureTheory ProbabilityTheory
namespace YangMills.Construction.MomentLaw
def farLevelSupportSitesStatement : Prop :=
  ForAllPoints fun Λ C _ _ S =>
    (∀ i : Fin Λ.k, ((S.data.supportSites Λ.stepParams.side S.lastSeparated i).card : ℝ) ≤
      C 0 * (S.range : ℝ) ^ 4) ∧
    (S.radius : ℝ) ≤ C 0 * (S.range : ℝ) ∧
    ∀ u, S.lastSeparated ≤ u → u ≤ S.data.windowLevel → ∀ (i : Fin Λ.k),
      ∀ y ∈ S.data.supportSites Λ.stepParams.side u i,
        S.data.distFromCenter Λ.stepParams.side u y ≤ S.radius
end YangMills.Construction.MomentLaw
end
