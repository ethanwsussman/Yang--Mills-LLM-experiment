import YangMills.Construction.ResponseInTheExpansion.CasesOfAStepCarryAFunction
import Mathlib
set_option autoImplicit false
noncomputable section
open MeasureTheory
namespace YangMills.Construction.ResponseInTheExpansion
open TorusFields TorusLumps StepSettings StepCosts
open Classical in
def coarseMassWith (R : StepSetup) {n : ℕ} [NeZero n] (C : Finset (TorusSite n)) (V : TorusField n)
    (H : (Yt : Finset (TorusSite (n * R.params.side))) → TorusField (n * R.params.side) → (Yt → R.labels.Ω) → ENNReal)
    (q : CoarseState R n) : ENNReal :=
  ∑ bad ∈ (markedBonds R C).powerset, ∑ Yt : Finset (TorusSite (n * R.params.side)), ∑ b : BaseChoice R.params.side n,
    configurationMassWith R C V bad Yt b (H Yt) q
def massOverStepStatement : Prop :=
  ∀ R : StepSetup, R.IsWellPosed → ∀ (n : ℕ) [NeZero n], IsBlockTorusSide R.params n →
    ∀ H : (Yt : Finset (TorusSite (n * R.params.side))) → TorusField (n * R.params.side) → (Yt → R.labels.Ω) → ℝ,
      (∀ Yt : Finset (TorusSite (n * R.params.side)),
        Measurable fun p : TorusField (n * R.params.side) × (Yt → R.labels.Ω) => H Yt p.1 p.2) →
      (∀ Yt W ωt, 0 ≤ H Yt W ωt) →
      (open Classical in
        ∫⁻ W, ∑ Yt ∈ Finset.univ.filter (IsHullState R.params (clusterRange R.coupling) W),
          ∫⁻ ωt, ENNReal.ofReal (R.labelWeight (n * R.params.side) W Yt ωt * H Yt W ωt)
            ∂(Measure.pi fun _ : Yt => R.labels.μ)
          ∂(fieldHaar (n * R.params.side))) =
        ∫⁻ V, (open Classical in ∑ Y ∈ Finset.univ.filter (IsHullState R.params R.nextRange V),
          ∫⁻ ω, coarseMassWith R (hotCoreSites R V) V (fun Yt W ωt => ENNReal.ofReal (H Yt W ωt)) ⟨Y, ω⟩
            ∂(Measure.pi fun _ : Y => coarseLabelMeasure R.labels.μ R.params.side)) ∂(fieldHaar n)
end YangMills.Construction.ResponseInTheExpansion
end
