import YangMills.Construction.ResponseInTheExpansion.LevelsOfAFlow
import YangMills.Construction.ResponseInTheExpansion.SupportsAlongTheLevels
import Mathlib
set_option autoImplicit false
noncomputable section
open MeasureTheory
namespace YangMills.Construction
namespace ResponseInTheExpansion
open RenormalizationStepParameters StepSettings TorusLumps TorusFields WeightedResponses ClusterExpansionOfAStep BlockAverages
def jointMomentMeasurableStatement : Prop :=
  ∃ rt₀ : ChainParameters → ℝ, (∀ c, 0 < rt₀ c) ∧ ∀ T : ParameterAssignment, T.Admissible → T.rt ≤ rt₀ T.toChainParameters →
    ∀ K : ResponseParameters, ∃ y₀ : ℝ, ∀ (y β : ℝ)
      (hL : ∀ c : ChainStage (T.stepParameters y), CoarseLabelFacts c.toStepSetup)
      (z₀ : StageWithResponse (T.stepParameters y)), y₀ ≤ y → IsInitialStage T y β z₀ → ∀ s : ℕ,
      StagesOnFlowUpTo T K y β hL z₀ s →
      ∀ (n : ℕ) [NeZero n], IsBlockTorusSide (T.stepParameters y) n → ∀ {ι : Type} (I : Finset ι)
        (f : ι → StageWeight hL T.lam (couplingsAlongFlow (T.stepParameters y) β) z₀ s n) (Y : Finset (TorusSite n)),
        open Classical in
        Measurable fun p : TorusField n × (Y → (flowStages T y β hL z₀ s).1.labels.Ω) =>
          if IsLiveState (T.stepParameters y) (flowStages T y β hL z₀ s).1.coupling
              (flowStages T y β hL z₀ s).1.labelWeight p.1 Y p.2 then
            jointMoment hL T.lam (couplingsAlongFlow (T.stepParameters y) β) z₀ s n I f p.1 Y p.2
          else 0
end ResponseInTheExpansion
end YangMills.Construction
end
