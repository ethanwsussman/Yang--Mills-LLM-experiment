import YangMills.Construction.LawByMomentsOfTheFlow.WindowOfTheLaw
import Mathlib
set_option autoImplicit false
noncomputable section
open MeasureTheory ProbabilityTheory
namespace YangMills.Construction.MomentLaw
def coldFineFieldStatement : Prop :=
  ForAllPoints fun Λ C _ X₀ S => X₀ ≤ S.scaleCoupling → ∀ (d n : ℕ) [NeZero n], d < S.logIndex →
    n = S.levelSide (S.lastSeparated + d + 1) →
    ∀ (V : TorusFields.TorusField n) (Y : Finset (TorusFields.TorusSite n)), S.IsGoodConfig (S.lastSeparated + d + 1) n V Y →
    (∀ N : ℕ, (coldFreeLaw (S.tower.stage (S.lastSeparated + d)).toStepSetup (S.smoothedField (S.lastSeparated + d + 1) n V))
        {η | ¬ boxCurvature (S.originSite (S.lastSeparated + d) (n * Λ.stepParams.side)) (2 * S.rangeSq)
          ((coldSettingOver (S.tower.stage (S.lastSeparated + d)).toStepSetup (S.smoothedField (S.lastSeparated + d + 1) n V)).field η) ≤
            S.scaleCoupling ^ (-(1 / 4) : ℝ)} ≤
      ENNReal.ofReal (C N * S.scaleCoupling ^ (-(N : ℝ)))) ∧
    (∀ (p : WeightedResponses.OrientedPlaquette (n * Λ.stepParams.side)) (q : ℕ), 1 ≤ q →
      (TorusFields.supDist p.1.1 (S.originSite (S.lastSeparated + d) (n * Λ.stepParams.side)) : ℝ) ≤ 2 * S.rangeSq →
      eLpNorm (Set.indicator {η | boxCurvature (S.originSite (S.lastSeparated + d) (n * Λ.stepParams.side)) (2 * S.rangeSq)
          ((coldSettingOver (S.tower.stage (S.lastSeparated + d)).toStepSetup (S.smoothedField (S.lastSeparated + d + 1) n V)).field η) ≤
            S.scaleCoupling ^ (-(1 / 4) : ℝ)}
        (fun η => curlNorm (fun e b => toColourForm (axialCoords Λ.stepParams
            ((coldSettingOver (S.tower.stage (S.lastSeparated + d)).toStepSetup (S.smoothedField (S.lastSeparated + d + 1) n V)).field η)
            (S.originSite (S.lastSeparated + d) (n * Λ.stepParams.side))) e b -
          (fun e b => pushColours Λ.stepParams.coupling Λ.table.ρA Λ.stepParams.side (S.lastSeparated + d)
              (S.cutoffColourForm (S.lastSeparated + d + 1) n V) e b +
            freeCoordForm (coldSettingOver (S.tower.stage (S.lastSeparated + d)).toStepSetup (S.smoothedField (S.lastSeparated + d + 1) n V)) η e b) e b) p.1))
        (q : ENNReal) (coldFreeLaw (S.tower.stage (S.lastSeparated + d)).toStepSetup (S.smoothedField (S.lastSeparated + d + 1) n V)) ≤
      ENNReal.ofReal (C q * (1 + (TorusFields.supDist p.1.1 (S.originSite (S.lastSeparated + d) (n * Λ.stepParams.side)) : ℝ)) ^ 2 *
        (S.localCurvature (S.lastSeparated + d + 1) n V + S.scaleCoupling ^ (-(1 / 2) : ℝ)) ^ 2)) ∧
    ∀ q : ℕ, 1 ≤ q →
      ENNReal.ofReal (S.scaleCoupling ^ ((1 : ℝ) / 2)) *
        weightedCurvatureNorm (coldFreeLaw (S.tower.stage (S.lastSeparated + d)).toStepSetup (S.smoothedField (S.lastSeparated + d + 1) n V))
          (S.distanceWeight (S.lastSeparated + d) (n * Λ.stepParams.side)) (q : ENNReal)
          (Set.indicator {η | boxCurvature (S.originSite (S.lastSeparated + d) (n * Λ.stepParams.side)) (2 * S.rangeSq)
              ((coldSettingOver (S.tower.stage (S.lastSeparated + d)).toStepSetup (S.smoothedField (S.lastSeparated + d + 1) n V)).field η) ≤
                S.scaleCoupling ^ (-(1 / 4) : ℝ)}
            fun η => toColourForm (cutoffCoords Λ.stepParams
              ((coldSettingOver (S.tower.stage (S.lastSeparated + d)).toStepSetup (S.smoothedField (S.lastSeparated + d + 1) n V)).field η)
              (S.originSite (S.lastSeparated + d) (n * Λ.stepParams.side)) S.rangeSq)) ≤
        ENNReal.ofReal (C q * (1 + S.scaleCoupling ^ ((1 : ℝ) / 2) * S.localCurvature (S.lastSeparated + d + 1) n V)) ∧
      ENNReal.ofReal (S.scaleCoupling ^ ((1 : ℝ) / 2)) *
        weightedCurvatureNorm (coldFreeLaw (S.tower.stage (S.lastSeparated + d)).toStepSetup (S.smoothedField (S.lastSeparated + d + 1) n V))
          (S.distanceWeight (S.lastSeparated + d) (n * Λ.stepParams.side)) (q : ENNReal)
          (Set.indicator {η | boxCurvature (S.originSite (S.lastSeparated + d) (n * Λ.stepParams.side)) (2 * S.rangeSq)
              ((coldSettingOver (S.tower.stage (S.lastSeparated + d)).toStepSetup (S.smoothedField (S.lastSeparated + d + 1) n V)).field η) ≤
                S.scaleCoupling ^ (-(1 / 4) : ℝ)}
            fun η => (fun e b => pushColours Λ.stepParams.coupling Λ.table.ρA Λ.stepParams.side (S.lastSeparated + d)
                (S.cutoffColourForm (S.lastSeparated + d + 1) n V) e b +
              freeCoordForm (coldSettingOver (S.tower.stage (S.lastSeparated + d)).toStepSetup (S.smoothedField (S.lastSeparated + d + 1) n V)) η e b)) ≤
        ENNReal.ofReal (C q * (1 + S.scaleCoupling ^ ((1 : ℝ) / 2) * S.localCurvature (S.lastSeparated + d + 1) n V))
end YangMills.Construction.MomentLaw
end
