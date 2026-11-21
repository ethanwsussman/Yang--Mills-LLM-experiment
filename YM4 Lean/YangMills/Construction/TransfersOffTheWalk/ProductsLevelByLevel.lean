import YangMills.Construction.FreeEnergiesOfTheFlow.ProductsOnATowerDefs
import YangMills.Construction.TransfersOffTheWalk.ProductsAlongTheChain
import Mathlib
set_option autoImplicit false
noncomputable section
open MeasureTheory
namespace YangMills.Construction.TransfersOffTheWalk
open TorusFields TorusLumps StepSettings WeightedResponses FreeEnergies ResponseInTheExpansion ClusterExpansionOfAStep
def productInductionStatement : Prop :=
  AtResponseParameters fun Tb Kr y => ∀ p : ℕ, ∃ C : ℝ, 0 ≤ C ∧
    ∀ (T : StageTower (Tb.stepParameters y)) (S : ScoredStageTower T) (β : ℝ) (f : Fin p → FinePlaquetteFunction),
      S.params = Kr →
      (∀ (s n : ℕ) [NeZero n] (I : Finset (Fin p)), S.FollowsFlow β s → CouplingsAboveFloor (Tb.stepParameters y) β s →
        IsBlockTorusSide (Tb.stepParameters y) n →
        HasConditionalMean T β s n (fun u => ∏ i ∈ I, completedCentered S (f i) s n u)) ∧
      (∀ (n : ℕ) [NeZero n] (I : Finset (Fin p)), S.FollowsFlow β 0 → CouplingsAboveFloor (Tb.stepParameters y) β 0 →
        IsBlockTorusSide (Tb.stepParameters y) n →
        ∀ᵐ u ∂(markedSampleLaw T β 0 n),
          conditionalProduct S β f I 0 n u = ∏ i ∈ I, fittedResponse S (f i) 0 n (stageState T 0 n u)) ∧
      ∀ (t n : ℕ) [NeZero n] (I : Finset (Fin p)) (D : ℕ) (Err : Finset (Fin p) → ℝ),
        S.FollowsFlow β (t + 1) → CouplingsAboveFloor (Tb.stepParameters y) β (t + 1) →
        IsBlockTorusSide (Tb.stepParameters y) n →
        (∀ i, weightNorm (Tb.stepParameters y).side (t + 1)
          (fineWeight (f i) (fineSide (Tb.stepParameters y).side (t + 1) n)) ≤ 1) →
        2 ^ 10 * (clusterRange (flowCoupling (Tb.stepParameters y) β t) : ℝ) ≤ D → 8 < D →
        SitesSeparated (fun i => functionSites (Tb.stepParameters y).side (f i) (t + 1) n) (D : ℝ) →
        (∀ J ⊆ I, 0 ≤ Err J) →
        (∀ J ⊆ I, ∀ᵐ v ∂(markedSampleLaw T β t (n * (Tb.stepParameters y).side)),
          |conditionalProduct S β f J t (n * (Tb.stepParameters y).side) v -
              ∏ i ∈ J, fittedResponse S (f i) t (n * (Tb.stepParameters y).side) (stageState T t _ v)| ≤
            Err J * ∏ i ∈ J, scoreMeanOver S (f i) t (n * (Tb.stepParameters y).side) (stageState T t _ v)) →
        ∀ᵐ u ∂(markedSampleLaw T β (t + 1) n),
          |conditionalProduct S β f I (t + 1) n u - ∏ i ∈ I, fittedResponse S (f i) (t + 1) n (stageState T (t + 1) n u)| ≤
            (C * (∑ i ∈ I, ((functionSites (Tb.stepParameters y).side (f i) t (n * (Tb.stepParameters y).side)).card : ℝ)) ^ 2 *
                Real.exp (-((Tb.stepParameters y).rt * (D : ℝ) / 2 ^ 7)) *
                ∏ i ∈ I, (4 * (Kr.C₀ *
                  ((functionSites (Tb.stepParameters y).side (f i) t (n * (Tb.stepParameters y).side)).card : ℝ))) +
              Real.exp (2 ^ I.card * (I.card.factorial : ℝ) *
                  Real.exp (-(7 * Tb.gasRate * flowCoupling (Tb.stepParameters y) β t))) *
                ∑ J ∈ I.powerset, Err J *
                  ∏ i ∈ I \ J, (2 * (Kr.C₀ *
                    ((functionSites (Tb.stepParameters y).side (f i) t (n * (Tb.stepParameters y).side)).card : ℝ)))) *
              ∏ i ∈ I, scoreMeanOver S (f i) (t + 1) n (stageState T (t + 1) n u)
end YangMills.Construction.TransfersOffTheWalk
end
