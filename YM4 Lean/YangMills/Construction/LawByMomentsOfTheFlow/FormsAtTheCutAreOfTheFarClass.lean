import YangMills.Construction.LawByMomentsOfTheFlow.FarCopiesInALimitField
import YangMills.Construction.LawByMomentsOfTheFlow.WindowInALimitField
import Mathlib
set_option autoImplicit false
noncomputable section
open MeasureTheory
namespace YangMills.Construction.MomentLaw
open TorusFields WeightedResponses ResponseInTheExpansion FreeEnergies
def caseFormsQuasiLocalStatement : Prop :=
  ForAllPoints fun Λ _ _ X₀ S => X₀ ≤ S.scaleCoupling → ∀ (u d n : ℕ) [NeZero n], n = S.levelSide (u + 1) →
    u + 1 ≤ S.data.windowLevel → u = S.lastSeparated + d → d ≤ S.logIndex →
    ∀ (B : Finset (Fin Λ.k)) (M : ℝ), (∀ W Y ω bad b, |S.goodCaseForms u d n B W Y ω bad b| ≤ M) →
      IsQuasiLocalCaseFunction (S.tower.stage u).toStepSetup (S.originSite u (n * Λ.stepParams.side))
          (8 * S.rangeSq + 2) 0 M ∅ (fun _ => 0) (S.goodCaseForms u d n B) ∧
      ∀ᵐ x ∂(markedSampleLaw S.tower S.β (u + 1) n),
        CaseIntegrableAtSample S.tower u n (fun _ => S.goodCaseForms u d n B) x
end YangMills.Construction.MomentLaw
end
