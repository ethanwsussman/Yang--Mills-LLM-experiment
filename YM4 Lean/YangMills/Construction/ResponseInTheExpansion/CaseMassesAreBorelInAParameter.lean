import YangMills.Construction.ClusterExpansionOfAStep.StatesOfAStep
import Mathlib
set_option autoImplicit false
noncomputable section
open MeasureTheory
namespace YangMills.Construction.ResponseInTheExpansion
open TorusFields TorusLumps StepSettings StepCosts
open Classical in
def configurationMassOf (R : StepSetup) {n : ℕ} [NeZero n] (C : Finset (TorusSite n))
    (bad : Finset (TorusBond (n * R.params.side))) (Yt : Finset (TorusSite (n * R.params.side)))
    (b : BaseChoice R.params.side n) (G : TorusField (n * R.params.side) → (Yt → R.labels.Ω) → ENNReal)
    (q : CoarseState R n) : ENNReal :=
  ∫⁻ W, ∫⁻ ν : q.unlabelled Yt → R.labels.Ω,
      (if IsHullState R.params R.range (q.fieldWithStoredLinks W) Yt ∧
          coarseStateOf R C (q.fieldWithStoredLinks W) Yt (q.fillLabels Yt ν) bad b = q then
        G (q.fieldWithStoredLinks W) (q.fillLabels Yt ν) else 0)
      ∂(Measure.pi fun _ => R.labels.μ) ∂(fieldHaar (n * R.params.side))
def ConfigurationMassMeasurable : Prop :=
  ∀ (R : StepSetup) (n : ℕ) [NeZero n] (C : Finset (TorusSite n)) (bad : Finset (TorusBond (n * R.params.side)))
    (Yt : Finset (TorusSite (n * R.params.side))) (b : BaseChoice R.params.side n) (Ξ : Type) [MeasurableSpace Ξ]
    (G : Ξ → TorusField (n * R.params.side) → (Yt → R.labels.Ω) → ENNReal),
    (Measurable fun p : Ξ × TorusField (n * R.params.side) × (Yt → R.labels.Ω) => G p.1 p.2.1 p.2.2) →
    (∀ ξ W ωt, ¬ IsHullState R.params R.range W Yt → G ξ W ωt = 0) →
    Measurable fun p : Ξ × (coarseHull R.params.side R.range R.nextRange bad Yt C →
        CoarseLabel R.labels.Ω R.params.side) =>
      configurationMassOf R C bad Yt b (G p.1) ⟨coarseHull R.params.side R.range R.nextRange bad Yt C, p.2⟩
end YangMills.Construction.ResponseInTheExpansion
end
