import YangMills.Construction.LawByMomentsOfTheFlow.ChartOfTheColdSetting
import YangMills.Construction.LawByMomentsOfTheFlow.GaussianAgainstACutLaw
import Mathlib
set_option autoImplicit false
noncomputable section
open MeasureTheory ProbabilityTheory
namespace YangMills.Construction.MomentLaw
def potentialGradientBoundsStatement : Prop :=
  ForAllPoints fun Λ C _ X₀ S => X₀ ≤ S.scaleCoupling → ∀ (d n : ℕ) [NeZero n], d < S.logIndex →
    n = S.levelSide (S.lastSeparated + d + 1) →
    ∀ (V : TorusFields.TorusField n) (Y : Finset (TorusFields.TorusSite n)),
      S.IsGoodConfig (S.lastSeparated + d + 1) n V Y →
    (∀ j : Fin 3 × ChartBondIndex Λ.stepParams.side (S.lastSeparated + d) n,
      |fderiv ℝ (chartPotential (S.tower.stage (S.lastSeparated + d)).toStepSetup (S.lastSeparated + d)
        (S.smoothedField (S.lastSeparated + d + 1) n V)) 0 (MomentMethod.unitVariation j)| ≤ C 0) ∧
    ∀ j : Fin 3 × ChartBondIndex Λ.stepParams.side (S.lastSeparated + d) n,
      ∃ w : ChartBondIndex Λ.stepParams.side (S.lastSeparated + d) n → ℝ,
      (∀ b, 0 ≤ w b) ∧ ∑ b, w b ≤ C 0 ∧
      ∑ i, |fluctuationCov Λ.stepParams.coupling Λ.stepParams.side (S.coupling (S.lastSeparated + d))
          (S.lastSeparated + d) n j i| ≤
        C 0 * S.scaleCoupling⁻¹ ∧
      ∀ k : ColdStepAtMirrorFrames.BondField (ChartBondIndex Λ.stepParams.side (S.lastSeparated + d) n),
        (∀ b, ‖k b‖ < (S.tower.stage (S.lastSeparated + d)).toStepSetup.ballRadius) →
        |∑ i, fluctuationCov Λ.stepParams.coupling Λ.stepParams.side (S.coupling (S.lastSeparated + d))
              (S.lastSeparated + d) n j i *
            fderiv ℝ (chartPotential (S.tower.stage (S.lastSeparated + d)).toStepSetup (S.lastSeparated + d)
              (S.smoothedField (S.lastSeparated + d + 1) n V)) k (MomentMethod.unitVariation i) -
          k j.2 j.1| ≤
        C 0 * S.scaleCoupling⁻¹ * (1 + S.scaleCoupling * ∑ b, w b * (‖k b‖ ^ 2 +
          (1 + (TorusFields.supDist (TorusLumps.toTorusSite (n * Λ.stepParams.side) j.2.1.1)
            (S.originSite (S.lastSeparated + d) (n * Λ.stepParams.side)) : ℝ)) *
            S.localCurvature (S.lastSeparated + d + 1) n V * ‖k b‖))
end YangMills.Construction.MomentLaw
end
