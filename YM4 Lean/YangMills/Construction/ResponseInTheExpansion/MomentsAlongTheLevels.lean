import YangMills.Construction.ResponseInTheExpansion.LevelsOfAFlow
import YangMills.Construction.ResponseInTheExpansion.SupportsAlongTheLevels
import Mathlib
set_option autoImplicit false
noncomputable section
open MeasureTheory
namespace YangMills.Construction.ResponseInTheExpansion
open RenormalizationStepParameters StepSettings TorusLumps TorusFields WeightedResponses ClusterExpansionOfAStep BlockAverages
def momentsAlongStagesStatement : Prop :=
  ∃ rt₀ : ChainParameters → ℝ, (∀ c, 0 < rt₀ c) ∧ ∀ T : ParameterAssignment, T.Admissible → T.rt ≤ rt₀ T.toChainParameters →
    ∀ K : ResponseParameters, ∃ y₀ : ℝ, ∀ (y β : ℝ)
      (hL : ∀ c : ChainStage (T.stepParameters y), CoarseLabelFacts c.toStepSetup)
      (z₀ : StageWithResponse (T.stepParameters y)), y₀ ≤ y →
      IsInitialStage T y β z₀ → ∀ s : ℕ, StagesOnFlowUpTo T K y β hL z₀ s → ∀ (n : ℕ) [NeZero n],
      IsBlockTorusSide (T.stepParameters y) n → ∀ {ι : Type} (I : Finset ι) (D : ℕ → ℕ)
        (f : ι → StageWeight hL T.lam (couplingsAlongFlow (T.stepParameters y) β) z₀ s n),
        SeparatedAlong hL T.lam (couplingsAlongFlow (T.stepParameters y) β) z₀ I D s n f →
        ∫ W, ∏ i ∈ I, (curvatureObservable (f i) W -
            accumulatedShift hL T.lam (couplingsAlongFlow (T.stepParameters y) β) z₀ s n (f i))
          ∂(wilsonLaw β (fineSide (T.stepParameters y).side (flowStages T y β hL z₀ s).1.depth n)) =
        stateIntegral (flowStages T y β hL z₀ s).1.toStepSetup n
            (jointMoment hL T.lam (couplingsAlongFlow (T.stepParameters y) β) z₀ s n I f) /
          stateIntegral (flowStages T y β hL z₀ s).1.toStepSetup n fun _ _ _ => 1
end YangMills.Construction.ResponseInTheExpansion
end
