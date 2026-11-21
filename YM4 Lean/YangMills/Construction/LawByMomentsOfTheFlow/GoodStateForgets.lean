import YangMills.Construction.LawByMomentsOfTheFlow.WindowOfTheLaw
import Mathlib
set_option autoImplicit false
noncomputable section
open MeasureTheory ProbabilityTheory
namespace YangMills.Construction.MomentLaw
def goodStateMeanForgetsStatement : Prop :=
  ForAllPoints fun Λ _ _ X₀ S => X₀ ≤ S.scaleCoupling → ∀ (d n : ℕ) [NeZero n], d < S.logIndex → n = S.levelSide (S.lastSeparated + d + 1) →
    ∀ (V : TorusFields.TorusField n) (Y : Finset (TorusFields.TorusSite n)) (ω : Y → (S.tower.stage (S.lastSeparated + d + 1)).labels.Ω),
    S.IsGoodConfig (S.lastSeparated + d + 1) n V Y →
    0 < StepSettings.coarseStateWeight (S.tower.stage (S.lastSeparated + d)).toStepSetup
      (StepSettings.hotCoreSites (S.tower.stage (S.lastSeparated + d)).toStepSetup V) V ⟨Y, ω⟩ →
    ∀ (f : TorusFields.TorusField (n * Λ.stepParams.side) → Finset (TorusFields.TorusSite (n * Λ.stepParams.side)) → ℝ) (M : ℝ),
    (∀ W Yt, |f W Yt| ≤ M) →
    (∀ Yt, Measurable fun W => f W Yt) → (∀ g W Yt, f (TorusFields.gaugeTransform g W) Yt = f W Yt) →
    (∀ W W' Yt Yt', (∀ c : TorusFields.TorusBond (n * Λ.stepParams.side),
        c.1 ∈ ResponseInTheExpansion.supBall (S.originSite (S.lastSeparated + d) (n * Λ.stepParams.side)) (8 * S.rangeSq) →
        c.1 + TorusFields.unitStep (n * Λ.stepParams.side) c.2 ∈
          ResponseInTheExpansion.supBall (S.originSite (S.lastSeparated + d) (n * Λ.stepParams.side)) (8 * S.rangeSq) →
        W c.1 c.2 = W' c.1 c.2) →
      Yt ∩ ResponseInTheExpansion.supBall (S.originSite (S.lastSeparated + d) (n * Λ.stepParams.side)) (8 * S.rangeSq) =
        Yt' ∩ ResponseInTheExpansion.supBall (S.originSite (S.lastSeparated + d) (n * Λ.stepParams.side)) (8 * S.rangeSq) →
      f W Yt = f W' Yt') →
    |WeightedResponses.caseMean (S.tower.stage (S.lastSeparated + d)).toStepSetup
          (StepSettings.hotCoreSites (S.tower.stage (S.lastSeparated + d)).toStepSetup V) V ⟨Y, ω⟩ (fun W Yt _ _ _ => f W Yt) -
        coldExpectation (S.tower.stage (S.lastSeparated + d)).toStepSetup (S.smoothedField (S.lastSeparated + d + 1) n V)
          (fun η => f ((coldSettingOver (S.tower.stage (S.lastSeparated + d)).toStepSetup
            (S.smoothedField (S.lastSeparated + d + 1) n V)).field η) ∅)| ≤
      M * Real.exp (-(S.scaleCoupling ^ ((1 : ℝ) / 200)))
end YangMills.Construction.MomentLaw
end
