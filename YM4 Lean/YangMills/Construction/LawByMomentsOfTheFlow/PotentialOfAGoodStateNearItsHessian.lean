import YangMills.Construction.ColdStepAtMirrorFrames.FramesAgainstTheLeastField
import YangMills.Construction.LawByMomentsOfTheFlow.ChartOfTheColdSetting
import YangMills.Construction.LawByMomentsOfTheFlow.GaussianAgainstACutLaw
import YangMills.Construction.ResponseInTheExpansion.InverseOfACoordinateHessian
import Mathlib
set_option autoImplicit false
noncomputable section
namespace YangMills.Construction.MomentLaw
open TorusFields StepSettings WeightedResponses LinearResponse MomentMethod ColdStepAtMirrorFrames
def goodStatePotentialNearHessianStatement : Prop :=
  ForAllPoints fun Λ C _ X₀ S => X₀ ≤ S.scaleCoupling →
    ∀ (d n : ℕ) [NeZero n], d < S.logIndex → n = S.levelSide (S.lastSeparated + d + 1) →
    ∀ (V : TorusField n) (Y : Finset (TorusSite n)), S.IsGoodConfig (S.lastSeparated + d + 1) n V Y →
    ∀ k : BondField (ChartBondIndex Λ.stepParams.side (S.lastSeparated + d) n),
      (∀ b, ‖k b‖ < (S.tower.stage (S.lastSeparated + d)).toStepSetup.ballRadius) →
    ∀ j : Fin 3 × ChartBondIndex Λ.stepParams.side (S.lastSeparated + d) n,
      |fderiv ℝ (chartPotential (S.tower.stage (S.lastSeparated + d)).toStepSetup (S.lastSeparated + d)
            (S.smoothedField (S.lastSeparated + d + 1) n V)) k (unitVariation j) -
          S.coupling (S.lastSeparated + d) * ∑ r : ChartBondIndex Λ.stepParams.side (S.lastSeparated + d) n × Fin 3,
            bondCoordinateHessian (chartedEnergyAt Λ.stepParams.coupling
              (frameCoordField false Λ.stepParams.coupling Λ.table.ρA
                (S.tower.stage (S.lastSeparated + d)).toStepSetup.frameReach
                (readAtLevel (torusFrame Λ.stepParams.side (S.lastSeparated + d) n)
                  (torusFrame Λ.stepParams.side (S.lastSeparated + d) n).top
                  (S.smoothedField (S.lastSeparated + d + 1) n V)))
              (readAtLevel (torusFrame Λ.stepParams.side (S.lastSeparated + d) n)
                (torusFrame Λ.stepParams.side (S.lastSeparated + d) n).top
                (S.smoothedField (S.lastSeparated + d + 1) n V)))
              (j.2, j.1) r * k r.1 r.2| ≤
        C 0 * (1 + S.coupling (S.lastSeparated + d) *
          (∑ b, Real.exp (-(Λ.table.δ₁ / 2 * chordBondDist (torusFrame Λ.stepParams.side (S.lastSeparated + d) n) j.2 b)) *
            ‖k b‖) ^ 2)
end YangMills.Construction.MomentLaw
end
