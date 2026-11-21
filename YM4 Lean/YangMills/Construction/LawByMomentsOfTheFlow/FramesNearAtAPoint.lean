import YangMills.Construction.LawByMomentsOfTheFlow.FineFieldOverACutTop
import Mathlib
set_option autoImplicit false
noncomputable section
namespace YangMills.Construction.MomentLaw
def framesNearResponseAt (Λ : MomentParameters) : Prop :=
  ∃ (κ X₀ : ℝ), 1 ≤ κ ∧ 1 ≤ X₀ ∧ ∀ S : MomentPoint Λ, X₀ ≤ S.scaleCoupling → ∀ (d n : ℕ) [NeZero n], d < S.logIndex →
    n = S.levelSide (S.lastSeparated + d + 1) →
    ∀ (V : TorusFields.TorusField n) (Y : Finset (TorusFields.TorusSite n)),
      S.IsGoodConfig (S.lastSeparated + d + 1) n V Y →
      FramesNearResponse ((S.tower.stage (S.lastSeparated + d)).toStepSetup)
        (S.cutoffLie (S.lastSeparated + d + 1) n V)
        (ResponseInTheExpansion.responseOfLieForm Λ.stepParams.coupling Λ.table.ρA Λ.stepParams.side (S.lastSeparated + d)
          (S.cutoffLie (S.lastSeparated + d + 1) n V))
        (S.originSite (S.lastSeparated + d) (n * Λ.stepParams.side))
        (2 * S.rangeSq + 6) (S.localCurvature (S.lastSeparated + d + 1) n V) (S.scaleCoupling ^ (-2 : ℝ)) κ
def framesNearResponseStatement : Prop := ForAllParameters framesNearResponseAt
end YangMills.Construction.MomentLaw
end
