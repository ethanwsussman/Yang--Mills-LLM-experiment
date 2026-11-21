import YangMills.Construction.LawByMomentsOfTheFlow.GaussianChainOfTheLaw
import YangMills.Construction.LawByMomentsOfTheFlow.WindowOfTheLaw
import Mathlib
set_option autoImplicit false
noncomputable section
open MeasureTheory ProbabilityTheory
namespace YangMills.Construction.MomentLaw
def fluctuationMeanOfGoodStateStatement : Prop :=
  ForAllPoints fun Λ C _ X₀ S => X₀ ≤ S.scaleCoupling → ∀ (d n : ℕ) [NeZero n], d < S.logIndex → n = S.levelSide (S.lastSeparated + d + 1) →
    ∀ (V : TorusFields.TorusField n) (Y : Finset (TorusFields.TorusSite n)), S.IsGoodConfig (S.lastSeparated + d + 1) n V Y →
    ∀ B : Finset (Fin Λ.k),
    |coldExpectation (S.tower.stage (S.lastSeparated + d)).toStepSetup (S.smoothedField (S.lastSeparated + d + 1) n V)
        (fun η => S.formProductMean d (n * Λ.stepParams.side) B (fun e b =>
          pushColours Λ.stepParams.coupling Λ.table.ρA Λ.stepParams.side (S.lastSeparated + d)
            (S.cutoffColourForm (S.lastSeparated + d + 1) n V) e b +
          freeCoordForm (coldSettingOver (S.tower.stage (S.lastSeparated + d)).toStepSetup
            (S.smoothedField (S.lastSeparated + d + 1) n V)) η e b)) -
        S.formProductMean (d + 1) n B (S.cutoffColourForm (S.lastSeparated + d + 1) n V)| ≤
      C 0 * (S.range : ℝ) ^ (4 * B.card + 1) * S.scaleCoupling ^ (-(1 / 2) : ℝ) *
        (1 + S.scaleCoupling ^ ((1 : ℝ) / 2) * S.localCurvature (S.lastSeparated + d + 1) n V) ^ (2 * B.card)
end YangMills.Construction.MomentLaw
end
