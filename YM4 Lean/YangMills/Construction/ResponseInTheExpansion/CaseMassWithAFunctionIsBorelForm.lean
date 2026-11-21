import YangMills.Construction.ClusterExpansionOfAStep.StepAtFixedParameters
import YangMills.Construction.ResponseInTheExpansion.CasesOfAStepCarryAFunction
import Mathlib
set_option autoImplicit false
noncomputable section
open MeasureTheory
namespace YangMills.Construction
namespace ResponseInTheExpansion
open TorusFields TorusLumps StepSettings RenormalizationStepParameters StepCosts
def ConfigurationMassMeasurability : Prop :=
  ∀ T : ParameterAssignment, T.Admissible → ∀ y : ℝ, ∀ R : StepSetup, R.OnParameters T y → R.IsWellPosed →
    ∀ (n : ℕ) [NeZero n], IsBlockTorusSide R.params n →
      (∀ C : Finset (TorusSite n), MeasurableSet {V : TorusField n | hotCoreSites R V = C}) ∧
      (∀ Y : Finset (TorusSite n), MeasurableSet {V : TorusField n | IsHullState R.params R.nextRange V Y}) ∧
      (∀ (Yt : Finset (TorusSite (n * R.params.side))) (q : CoarseState R n),
        Measurable fun ν : q.unlabelled Yt → R.labels.Ω => q.fillLabels Yt ν) ∧
      (∀ (bad : Finset (TorusBond (n * R.params.side))) (Yt : Finset (TorusSite (n * R.params.side)))
        (b : BaseChoice R.params.side n)
        (G : TorusField n → TorusField (n * R.params.side) → (Yt → R.labels.Ω) → ENNReal),
        (Measurable fun p : TorusField n × TorusField (n * R.params.side) × (Yt → R.labels.Ω) =>
          G p.1 p.2.1 p.2.2) →
        ∀ Y : Finset (TorusSite n),
          Measurable fun p : TorusField n × (Y → CoarseLabel R.labels.Ω R.params.side) =>
            configurationMassWith R (hotCoreSites R p.1) p.1 bad Yt b (G p.1) ⟨Y, p.2⟩) ∧
      ∀ (C : Finset (TorusSite n)) (bad : Finset (TorusBond (n * R.params.side)))
        (Yt : Finset (TorusSite (n * R.params.side)))
        (b : BaseChoice R.params.side n) (q : CoarseState R n),
        MeasurableSet {p : TorusField (n * R.params.side) × (q.unlabelled Yt → R.labels.Ω) |
          IsHullState R.params R.range (q.fieldWithStoredLinks p.1) Yt ∧
            coarseStateOf R C (q.fieldWithStoredLinks p.1) Yt (q.fillLabels Yt p.2) bad b = q}
end ResponseInTheExpansion
end YangMills.Construction
end
