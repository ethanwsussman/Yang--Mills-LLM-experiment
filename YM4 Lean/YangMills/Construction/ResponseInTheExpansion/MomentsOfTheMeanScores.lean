import YangMills.Construction.FreeEnergiesOfTheFlow.ProductsOnATowerDefs
import Mathlib
set_option autoImplicit false
noncomputable section
open MeasureTheory
namespace YangMills.Construction.ResponseInTheExpansion
open FreeEnergies WeightedResponses TorusLumps RenormalizationStepParameters
def meanScoreMomentsStatement : Prop :=
  AtResponseParameters fun Tb Kr y => ∃ x₁ : ℝ, ∀ P : ℕ, 1 ≤ P → ∃ C : ℝ, 1 ≤ C ∧
    ∀ (T : StageTower (Tb.stepParameters y)) (S : ScoredStageTower T) (β : ℝ) (k m : ℕ)
      (g : FinePlaquetteFunction),
      S.params = Kr → S.FollowsFlow β k → CouplingsAboveFloor (Tb.stepParameters y) β k →
      x₁ ≤ ClusterExpansionOfAStep.flowCoupling (Tb.stepParameters y) β k →
      (Tb.stepParameters y).side * (Tb.stepParameters y).n₀ ≤ 2 * (Tb.stepParameters y).side ^ m →
      ∫⁻ u, ENNReal.ofReal (scoreMeanOver S g k (2 * (Tb.stepParameters y).side ^ m)
          (stageState T k _ u) ^ P)
          ∂(markedSampleLaw T β k (2 * (Tb.stepParameters y).side ^ m)) ≤
        ENNReal.ofReal ((C * (clusterRange (ClusterExpansionOfAStep.flowCoupling (Tb.stepParameters y) β k) : ℝ) ^ 4 *
          Real.log (ClusterExpansionOfAStep.flowCoupling (Tb.stepParameters y) β k)) ^ P)
end YangMills.Construction.ResponseInTheExpansion
end
