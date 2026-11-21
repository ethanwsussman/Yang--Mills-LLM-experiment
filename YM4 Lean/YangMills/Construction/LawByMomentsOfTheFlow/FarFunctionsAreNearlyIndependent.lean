import YangMills.Construction.LawByMomentsOfTheFlow.NearlyLocalFunctionsOfTheCases
import YangMills.Construction.LawByMomentsOfTheFlow.PointOfTheLaw
import Mathlib
set_option autoImplicit false
noncomputable section
open MeasureTheory
namespace YangMills.Construction.MomentLaw
def farCovarianceDecayStatement : Prop :=
  ForAllParameters fun Λ => ∀ (K : ℕ) (β Sz : ℝ) (Rr : ℕ), ∃ Cs : ℝ, ∀ S : MomentPoint Λ,
    S.data.windowLevel = K → S.β = β →
    ∀ (u n : ℕ) [NeZero n], u < K → n = S.levelSide (u + 1) →
      ∀ (V : TorusFields.TorusField n) (Y : Finset (TorusFields.TorusSite n))
      (ω : Y → (S.tower.stage (u + 1)).labels.Ω),
      0 < StepSettings.coarseStateWeight (S.tower.stage u).toStepSetup
        (StepSettings.hotCoreSites (S.tower.stage u).toStepSetup V) V ⟨Y, ω⟩ →
      ∀ (o o' : TorusFields.TorusSite (n * Λ.stepParams.side))
        (F G : WeightedResponses.CaseFunction (S.tower.stage u).toStepSetup n),
        IsNearlyLocalCaseFunction (S.tower.stage u).toStepSetup o Rr Sz F →
        IsNearlyLocalCaseFunction (S.tower.stage u).toStepSetup o' Rr Sz G →
        WeightedResponses.CaseIntegrable (S.tower.stage u).toStepSetup
          (StepSettings.hotCoreSites (S.tower.stage u).toStepSetup V) V ⟨Y, ω⟩ (fun _ _ _ _ _ => 1) ∧
        |WeightedResponses.caseMean (S.tower.stage u).toStepSetup
            (StepSettings.hotCoreSites (S.tower.stage u).toStepSetup V) V ⟨Y, ω⟩
            (fun W Yt ωt bad b => F W Yt ωt bad b * G W Yt ωt bad b) -
            WeightedResponses.caseMean (S.tower.stage u).toStepSetup
              (StepSettings.hotCoreSites (S.tower.stage u).toStepSetup V) V ⟨Y, ω⟩ F *
              WeightedResponses.caseMean (S.tower.stage u).toStepSetup
                (StepSettings.hotCoreSites (S.tower.stage u).toStepSetup V) V ⟨Y, ω⟩ G| ≤
          Cs * Real.exp (-(Λ.stepParams.rt * (TorusFields.supDist (TorusLumps.parentBlock Λ.stepParams.side o)
            (TorusLumps.parentBlock Λ.stepParams.side o') : ℝ) / 2 ^ 8))
end YangMills.Construction.MomentLaw
end
