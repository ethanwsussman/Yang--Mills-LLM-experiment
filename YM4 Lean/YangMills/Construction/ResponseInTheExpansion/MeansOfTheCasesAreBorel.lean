import YangMills.Construction.ClusterExpansionOfAStep.FactorsOfAStep
import YangMills.Construction.ClusterExpansionOfAStep.StepAtFixedParameters
import YangMills.Construction.ResponseInTheExpansion.ResponseOfAStep
import Mathlib
set_option autoImplicit false
noncomputable section
open MeasureTheory
namespace YangMills.Construction.WeightedResponses
open YangMills.Construction.TorusFields YangMills.Construction.StepSettings YangMills.Construction.StepCosts
def caseMeanMeasurableStatement : Prop :=
  ∀ T : RenormalizationStepParameters.ParameterAssignment, T.Admissible → ∃ y₀ : ℝ, ∀ y : ℝ, y₀ ≤ y →
    ∀ R : StepSetup, R.OnParameters T y → R.IsWellPosed →
    ∀ (n : ℕ) [NeZero n], TorusLumps.IsBlockTorusSide R.params n →
    ∀ (Y : Finset (TorusSite n)) (H : TorusField n → CaseFunction R n),
      (∀ (Yt : Finset (TorusSite (n * R.params.side))) (bad : Finset (TorusBond (n * R.params.side)))
          (b : BaseChoice R.params.side n),
        open Classical in
        Measurable fun p : TorusField n × TorusField (n * R.params.side) × (Yt → R.labels.Ω) =>
          if IsLiveState R.params R.coupling R.labelWeight p.2.1 Yt p.2.2 then H p.1 p.2.1 Yt p.2.2 bad b
          else 0) →
      open Classical in
      Measurable fun p : TorusField n × (Y → TorusLumps.CoarseLabel R.labels.Ω R.params.side) =>
        if TorusLumps.IsHullState R.params R.nextRange p.1 Y then
          caseMean R (hotCoreSites R p.1) p.1 ⟨Y, p.2⟩ (H p.1)
        else 0
end YangMills.Construction.WeightedResponses
end
