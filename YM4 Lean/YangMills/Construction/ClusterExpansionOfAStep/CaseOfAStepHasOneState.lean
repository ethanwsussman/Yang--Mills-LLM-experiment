import YangMills.Construction.ClusterExpansionOfAStep.CaseOfAStep
import YangMills.Construction.ClusterExpansionOfAStep.FactorsOfAStep
import Mathlib
set_option autoImplicit false
noncomputable section
open MeasureTheory
namespace YangMills.Construction.ClusterExpansionOfAStep
open BlockAverages LumpContours TorusLumps TorusFields StepSettings StepCosts
def ConfigurationSupportedOnCoarseHull : Prop :=
  ∀ R : StepSetup, R.IsWellPosed → ∀ (n : ℕ) [NeZero n], R.params.n₀ ≤ n →
    ∀ (C : Finset (TorusSite n)) (V : TorusField n)
    (bad : Finset (TorusBond (n * R.params.side))) (Yt : Finset (TorusSite (n * R.params.side)))
    (b : StepCosts.BaseChoice R.params.side n),
    (∀ q : CoarseState R n, q.1 ≠ coarseHull R.params.side R.range R.nextRange bad Yt C →
        configurationMass R C V bad Yt b q = 0) ∧
    Measurable (fun ω =>
      configurationMass R C V bad Yt b ⟨coarseHull R.params.side R.range R.nextRange bad Yt C, ω⟩) ∧
    ∫⁻ ω, configurationMass R C V bad Yt b ⟨coarseHull R.params.side R.range R.nextRange bad Yt C, ω⟩
        ∂(Measure.pi fun _ => coarseLabelMeasure R.labels.μ R.params.side) =
      ∫⁻ W, ∫⁻ ωt : Yt → R.labels.Ω, configurationWeight R C V bad Yt b W ωt
        ∂(Measure.pi fun _ => R.labels.μ) ∂(fieldHaar (n * R.params.side))
end YangMills.Construction.ClusterExpansionOfAStep
end
