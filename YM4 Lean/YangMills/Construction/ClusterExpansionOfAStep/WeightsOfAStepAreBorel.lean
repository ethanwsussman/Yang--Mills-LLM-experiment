import YangMills.Construction.ClusterExpansionOfAStep.CaseOfAStep
import YangMills.Construction.ClusterExpansionOfAStep.FactorsOfAStep
import Mathlib
set_option autoImplicit false
noncomputable section
open MeasureTheory
namespace YangMills.Construction
namespace ClusterExpansionOfAStep
def ConfigurationWeightMeasurable : Prop :=
  ∀ R : StepSettings.StepSetup, R.IsWellPosed → ∀ (n : ℕ) [NeZero n], R.params.n₀ ≤ n →
    ∀ (C : Finset (TorusFields.TorusSite n)) (V : TorusFields.TorusField n)
    (bad : Finset (TorusFields.TorusBond (n * R.params.side)))
    (Yt : Finset (TorusFields.TorusSite (n * R.params.side)))
    (b : StepCosts.BaseChoice R.params.side n),
    Measurable fun q : TorusFields.TorusField (n * R.params.side) × (Yt → R.labels.Ω) =>
      configurationWeight R C V bad Yt b q.1 q.2
end ClusterExpansionOfAStep
end YangMills.Construction
end
