import YangMills.Construction.LawByMomentsOfTheFlow.WindowOfTheLaw
import Mathlib
set_option autoImplicit false
noncomputable section
open MeasureTheory ProbabilityTheory
namespace YangMills.Construction.MomentLaw
open TorusFields WeightedResponses
def carriedCutCurvatureStatement : Prop :=
  ForAllPoints fun Λ C _ X₀ S => X₀ ≤ S.scaleCoupling → ∀ (d n : ℕ) [NeZero n], d < S.logIndex →
    n = S.levelSide (S.lastSeparated + d + 1) →
    ∀ (V : TorusField n) (Y : Finset (TorusSite n)), S.IsGoodConfig (S.lastSeparated + d + 1) n V Y →
    ∀ p : OrientedPlaquette (n * Λ.stepParams.side),
      S.distanceWeight (S.lastSeparated + d) (n * Λ.stepParams.side) p.1 *
          curlNorm (fun e b => pushColours Λ.stepParams.coupling Λ.table.ρA Λ.stepParams.side (S.lastSeparated + d)
            (S.cutoffColourForm (S.lastSeparated + d + 1) n V) e b) p.1 ≤
        C 0 * S.localCurvature (S.lastSeparated + d + 1) n V
end YangMills.Construction.MomentLaw
end
