import YangMills.Construction.ResponseInTheExpansion.ResponseOfAStep
import YangMills.Construction.ResponseInTheExpansion.StatesAlongTheChain
import Mathlib
set_option autoImplicit false
noncomputable section
open MeasureTheory
namespace YangMills.Construction.WeightedResponses
open YangMills.Construction.TorusFields YangMills.Construction.StepSettings YangMills.Construction.StepCosts
abbrev StepCaseState (R : StepSetup) (m : ℕ) : Type :=
  TorusField m × (Σ Y : Finset (TorusSite m), (Y → R.labels.Ω))
def stepJointLaw (R : StepSetup) (n : ℕ) [NeZero n] {A : Type} [MeasurableSpace A] (μ : Measure A)
    (st : A → StepCaseState R (n * R.params.side)) : Measure (A × StepOutcome R.params n) :=
  (μ.prod (stepReferenceMeasure R.params n)).withDensity fun u =>
    ENNReal.ofReal (stepOutcomeDensity R (st u.1).1 u.2)
def stepImage (R : StepSetup) {n : ℕ} [NeZero n] (q : StepCaseState R (n * R.params.side))
    (d : StepOutcome R.params n) : TorusField n × CoarseState R n :=
  (d.2.1, coarseStateOf R (hotCoreSites R d.2.1) q.1 q.2.1 q.2.2 d.2.2 d.1)
def caseValueAt {R : StepSetup} {n : ℕ} [NeZero n] (F : TorusField n → CaseFunction R n)
    (q : StepCaseState R (n * R.params.side)) (d : StepOutcome R.params n) : ℝ :=
  F d.2.1 q.1 q.2.1 q.2.2 d.2.2 d.1
def HasStateDensity (R : StepSetup) (n : ℕ) [NeZero n] (Z : ENNReal) {A : Type} [MeasurableSpace A]
    (μ : Measure A) (st : A → StepCaseState R (n * R.params.side)) : Prop :=
  ∀ G : StepCaseState R (n * R.params.side) → ENNReal, Measurable G →
    Z * ∫⁻ a, G (st a) ∂μ = ∫⁻ W, (open Classical in
      ∑ Y ∈ Finset.univ.filter (TorusLumps.IsHullState R.params R.range W),
      ∫⁻ ω, G (W, ⟨Y, ω⟩) * ENNReal.ofReal (R.labelWeight (n * R.params.side) W Y ω)
        ∂(Measure.pi fun _ : Y => R.labels.μ))
      ∂(fieldHaar (n * R.params.side))
def conditionalMeanGivenCoarseState : Prop :=
  ∀ R : StepSetup, R.IsWellPosed → ∀ (n : ℕ) [NeZero n], R.params.n₀ ≤ n → R.params.side ∣ n →
    (∀ bad : Finset (TorusBond (n * R.params.side)),
      Measurable fun p : TorusField (n * R.params.side) × TorusField n => markLaw R p.1 p.2 bad) →
    (∀ a : Finset (TorusSite n), MeasurableSet {V : TorusField n | hotCoreSites R V = a}) →
    ∀ (A : Type) [MeasurableSpace A] (μ : Measure A) [SFinite μ]
      (st : A → StepCaseState R (n * R.params.side)), Measurable st →
    ∀ Z : ENNReal, Z ≠ 0 → Z ≠ ⊤ → HasStateDensity R n Z μ st → IsFiniteMeasure (stepJointLaw R n μ st) →
    ∀ (F : TorusField n → CaseFunction R n) (B : ℝ),
      (∀ (Yt : Finset (TorusSite (n * R.params.side))) (bad : Finset (TorusBond (n * R.params.side)))
          (b : BaseChoice R.params.side n),
        Measurable fun p : TorusField n × TorusField (n * R.params.side) × (Yt → R.labels.Ω) =>
          F p.1 p.2.1 Yt p.2.2 bad b) →
      (∀ V W Yt ωt bad b, |F V W Yt ωt bad b| ≤ B) →
      ((stepJointLaw R n μ st)[fun u : A × StepOutcome R.params n => caseValueAt F (st u.1) u.2 |
        MeasurableSpace.comap (fun u : A × StepOutcome R.params n => stepImage R (st u.1) u.2) inferInstance])
        =ᵐ[stepJointLaw R n μ st]
      fun u => caseMean R (hotCoreSites R u.2.2.1) u.2.2.1 (stepImage R (st u.1) u.2).2 (F u.2.2.1)
end YangMills.Construction.WeightedResponses
end
