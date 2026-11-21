import YangMills.Construction.LawByMomentsOfTheFlow.GaussianChainOfTheLaw
import YangMills.Construction.LawByMomentsOfTheFlow.WindowOfTheLaw
import Mathlib
set_option autoImplicit false
noncomputable section
open MeasureTheory ProbabilityTheory
namespace YangMills.Construction.MomentLaw
open TorusFields WeightedResponses ResponseInTheExpansion StepSettings
def formProductMeanStepStatement : Prop :=
  ForAllPoints fun Λ C _ X₀ S => X₀ ≤ S.scaleCoupling → ∀ (d n : ℕ) [NeZero n], d < S.logIndex →
    n = S.levelSide (S.lastSeparated + d + 1) →
    ∀ (V : TorusField n) (Y : Finset (TorusSite n))
      (ω : Y → (S.tower.stage (S.lastSeparated + d + 1)).labels.Ω),
      S.IsGoodConfig (S.lastSeparated + d + 1) n V Y →
    0 < coarseStateWeight (S.tower.stage (S.lastSeparated + d)).toStepSetup
      (hotCoreSites (S.tower.stage (S.lastSeparated + d)).toStepSetup V) V ⟨Y, ω⟩ →
    ∀ B : Finset (Fin Λ.k),
    |caseMean (S.tower.stage (S.lastSeparated + d)).toStepSetup
          (hotCoreSites (S.tower.stage (S.lastSeparated + d)).toStepSetup V) V ⟨Y, ω⟩ (fun W Yt _ _ _ =>
          open Classical in if S.IsGoodConfig (S.lastSeparated + d) (n * Λ.stepParams.side) W Yt then
            S.formProductMean d (n * Λ.stepParams.side) B
              (S.cutoffColourForm (S.lastSeparated + d) (n * Λ.stepParams.side) W) else 0) -
        S.formProductMean (d + 1) n B (S.cutoffColourForm (S.lastSeparated + d + 1) n V)| ≤
      C 0 * (S.range : ℝ) ^ (4 * B.card + 2) * S.scaleCoupling ^ (-(1 / 2) : ℝ) *
        (1 + S.scaleCoupling ^ ((1 : ℝ) / 2) * S.localCurvature (S.lastSeparated + d + 1) n V) ^ (2 * B.card + 1)
end YangMills.Construction.MomentLaw
end
