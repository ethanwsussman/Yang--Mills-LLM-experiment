import YangMills.Construction.ClusterExpansionOfAStep.CaseOfAStep
import YangMills.Construction.ClusterExpansionOfAStep.FactorsOfAStep
import Mathlib
set_option autoImplicit false
noncomputable section
open MeasureTheory
namespace YangMills.Construction
namespace ResponseInTheExpansion
open TorusFields TorusLumps StepSettings StepCosts ClusterExpansionOfAStep LumpContours BlockAverages
open Classical in
def configurationMassWith (R : StepSetup) {n : ℕ} [NeZero n] (C : Finset (TorusSite n)) (V : TorusField n)
    (bad : Finset (TorusBond (n * R.params.side))) (Yt : Finset (TorusSite (n * R.params.side)))
    (b : BaseChoice R.params.side n)
    (g : TorusField (n * R.params.side) → (Yt → R.labels.Ω) → ENNReal) (q : CoarseState R n) : ENNReal :=
  ∫⁻ W, ∫⁻ ν : q.unlabelled Yt → R.labels.Ω,
      (if IsHullState R.params R.range (q.fieldWithStoredLinks W) Yt ∧
          coarseStateOf R C (q.fieldWithStoredLinks W) Yt (q.fillLabels Yt ν) bad b = q then
        ENNReal.ofReal (stepWeight R C V (q.fieldWithStoredLinks W) Yt (q.fillLabels Yt ν) bad b) *
          g (q.fieldWithStoredLinks W) (q.fillLabels Yt ν) else 0)
      ∂(Measure.pi fun _ => R.labels.μ) ∂(fieldHaar (n * R.params.side))
def ConfigurationMassWithFunction : Prop :=
  ∀ R : StepSetup, R.IsWellPosed → ∀ (n : ℕ) [NeZero n], R.params.n₀ ≤ n →
    ∀ (C : Finset (TorusSite n)) (V : TorusField n)
    (bad : Finset (TorusBond (n * R.params.side))) (Yt : Finset (TorusSite (n * R.params.side)))
    (b : BaseChoice R.params.side n)
    (g : TorusField (n * R.params.side) → (Yt → R.labels.Ω) → ENNReal),
    (Measurable fun p : TorusField (n * R.params.side) × (Yt → R.labels.Ω) => g p.1 p.2) →
    (∀ q : CoarseState R n, q.1 ≠ coarseHull R.params.side R.range R.nextRange bad Yt C →
      configurationMassWith R C V bad Yt b g q = 0) ∧
    (∀ q : CoarseState R n, configurationMass R C V bad Yt b q = 0 →
      configurationMassWith R C V bad Yt b g q = 0) ∧
    Measurable (fun ω => configurationMassWith R C V bad Yt b g
      ⟨coarseHull R.params.side R.range R.nextRange bad Yt C, ω⟩) ∧
    ∫⁻ ω, configurationMassWith R C V bad Yt b g ⟨coarseHull R.params.side R.range R.nextRange bad Yt C, ω⟩
        ∂(Measure.pi fun _ => coarseLabelMeasure R.labels.μ R.params.side) =
      ∫⁻ W, ∫⁻ ωt : Yt → R.labels.Ω, configurationWeight R C V bad Yt b W ωt * g W ωt
        ∂(Measure.pi fun _ => R.labels.μ) ∂(fieldHaar (n * R.params.side))
end ResponseInTheExpansion
end YangMills.Construction
end
