import YangMills.Construction.FreeEnergiesOfTheFlow.ProductsOnATowerDefs
import Mathlib
set_option autoImplicit false
noncomputable section
open MeasureTheory
namespace YangMills.Construction.FreeEnergies
open StepGas TorusLumps StepSettings WeightedResponses
def ConditionalProductStepBound : Prop :=
  AtResponseParameters fun Tb Kr y => ∀ (β : ℝ) (T : StageTower (Tb.stepParameters y)) (S : ScoredStageTower T) (t : ℕ),
    S.params = Kr →
    S.FollowsFlow β (t + 1) → CouplingsAboveFloor (Tb.stepParameters y) β (t + 1) →
    ∀ (k : ℕ) (φ : Fin k → FinePlaquetteFunction) (n : ℕ) [NeZero n],
    IsBlockTorusSide (Tb.stepParameters y) n →
    (∀ i, weightNorm (Tb.stepParameters y).side t
        (fineWeight (φ i) (fineSide (Tb.stepParameters y).side t (n * (Tb.stepParameters y).side))) ≤ 1) →
    (∀ i, weightNorm (Tb.stepParameters y).side (t + 1)
        (fineWeight (φ i) (fineSide (Tb.stepParameters y).side (t + 1) n)) ≤ 1) →
    ∀ (I : Finset (Fin k)) (ε : ℝ) (μ δ : Finset (Fin k) → ℝ),
    (∀ G : GasGround (T.stage t).toStepSetup n, G.IsAdmissibleGround →
      CaseIntegrable (T.stage t).toStepSetup G.cut G.coarse G.state (fun W Y ω bad b =>
        ∏ i ∈ I, ResponseInTheExpansion.centeredSupportResponse (S.setup t) G.coarse (fineWeight (φ i) _) W Y ω bad b) ∧
      |caseMean (T.stage t).toStepSetup G.cut G.coarse G.state (fun W Y ω bad b =>
          ∏ i ∈ I, ResponseInTheExpansion.centeredSupportResponse (S.setup t) G.coarse (fineWeight (φ i) _) W Y ω bad b) -
        ∏ i ∈ I, caseMean (T.stage t).toStepSetup G.cut G.coarse G.state
          (ResponseInTheExpansion.centeredSupportResponse (S.setup t) G.coarse (fineWeight (φ i) _))| ≤
      ε * ∏ i ∈ I, ResponseInTheExpansion.meanSiteScore (coarseLabelScore S.params.s₁ (S.setup t).score)
        (functionSites (Tb.stepParameters y).side (φ i) (t + 1) n) G.state.1 G.state.2) →
    (∀ J ⊆ I, J.Nonempty → ∀ G : GasGround (T.stage t).toStepSetup n, G.IsAdmissibleGround →
      CaseIntegrable (T.stage t).toStepSetup G.cut G.coarse G.state (fun _ Y ω _ _ =>
        ∏ i ∈ J, ResponseInTheExpansion.meanSiteScore (S.setup t).score
          (functionSites (Tb.stepParameters y).side (φ i) t (n * (Tb.stepParameters y).side)) Y ω) ∧
      caseMean (T.stage t).toStepSetup G.cut G.coarse G.state (fun _ Y ω _ _ =>
        ∏ i ∈ J, ResponseInTheExpansion.meanSiteScore (S.setup t).score
          (functionSites (Tb.stepParameters y).side (φ i) t (n * (Tb.stepParameters y).side)) Y ω) ≤
      μ J * ∏ i ∈ J, ResponseInTheExpansion.meanSiteScore (coarseLabelScore S.params.s₁ (S.setup t).score)
        (functionSites (Tb.stepParameters y).side (φ i) (t + 1) n) G.state.1 G.state.2) →
    (∀ J ⊆ I, J.Nonempty → 0 ≤ δ J ∧ 0 ≤ μ J ∧
      ∀ᵐ a ∂(markedSampleLaw T β t (n * (Tb.stepParameters y).side)),
      |conditionalProduct S β φ J t (n * (Tb.stepParameters y).side) a -
          ∏ i ∈ J, fittedResponse S (φ i) t (n * (Tb.stepParameters y).side)
            (stageState T t _ a)| ≤
        δ J * ∏ i ∈ J, scoreMeanOver S (φ i) t (n * (Tb.stepParameters y).side)
          (stageState T t _ a)) →
    ∀ᵐ x ∂(markedSampleLaw T β (t + 1) n),
      |conditionalProduct S β φ I (t + 1) n x -
          ∏ i ∈ I, fittedResponse S (φ i) (t + 1) n (stageState T (t + 1) n x)| ≤
        (ε + ∑ J ∈ I.powerset.filter Finset.Nonempty, δ J * μ J *
            ∏ i ∈ I \ J, (2 * (S.params.C₀ *
              ((functionSites (Tb.stepParameters y).side (φ i) t (n * (Tb.stepParameters y).side)).card : ℝ)))) *
          ∏ i ∈ I, scoreMeanOver S (φ i) (t + 1) n (stageState T (t + 1) n x)
end YangMills.Construction.FreeEnergies
end
