import YangMills.Construction.FreeEnergiesOfTheFlow.ProductsOnATowerDefs
import Mathlib
set_option autoImplicit false
noncomputable section
open MeasureTheory
namespace YangMills.Construction.FreeEnergies
def fittedResponseIsConditionalMeanStatement : Prop :=
  AtResponseParameters fun Tb Kr y => ∀ (β : ℝ) (T : WeightedResponses.StageTower (Tb.stepParameters y))
    (S : ScoredStageTower T) (tp : ℕ), S.params = Kr →
    S.FollowsFlow β tp → CouplingsAboveFloor (Tb.stepParameters y) β tp → ∀ (f : FinePlaquetteFunction) (s : ℕ), s ≤ tp →
    ∀ (n : ℕ) [NeZero n], TorusLumps.IsBlockTorusSide (Tb.stepParameters y) n →
      (∃ fm : WeightedResponses.StageState T s n → ℝ, Measurable fm ∧
        (∀ (W : TorusFields.TorusField n) (Y : Finset (TorusFields.TorusSite n)) (ω : Y → (T.stage s).labels.Ω),
          WeightedResponses.IsLiveState (Tb.stepParameters y) (T.stage s).coupling (T.stage s).labelWeight W Y ω →
            fm (W, ⟨Y, ω⟩) = fittedResponse S f s n (W, ⟨Y, ω⟩)) ∧
        ∀ᵐ a ∂(WeightedResponses.markedSampleLaw T β s n),
          fm (WeightedResponses.stageState T s n a) = fittedResponse S f s n (WeightedResponses.stageState T s n a)) ∧
      (∀ᵐ a ∂(WeightedResponses.markedSampleLaw T β s n),
        fittedResponse S f s n (WeightedResponses.stageState T s n a) =
          ((WeightedResponses.markedSampleLaw T β s n)[completedCentered S f s n |
            WeightedResponses.stageSigma T s n]) a) ∧
      (s < tp → ∀ᵐ x ∂(WeightedResponses.markedSampleLaw T β (s + 1) n),
        WeightedResponses.caseMean (T.stage s).toStepSetup
            (StepSettings.hotCoreSites (T.stage s).toStepSetup x.2.2.1) x.2.2.1
            (WeightedResponses.stageState T (s + 1) n x).2
            (ResponseInTheExpansion.centeredSupportResponse (S.setup s) x.2.2.1 (fineWeight f _)) =
          fittedResponse S f (s + 1) n (WeightedResponses.stageState T (s + 1) n x))
end YangMills.Construction.FreeEnergies
end
