import YangMills.Construction.ResponseInTheExpansion.SupportsAlongTheLevels
import Mathlib
set_option autoImplicit false
noncomputable section
open MeasureTheory
namespace YangMills.Construction
namespace ResponseInTheExpansion
open StepSettings StepCosts TorusFields TorusLumps RenormalizationStepParameters WeightedResponses ClusterExpansionOfAStep
def stateMeasure (R : StepSetup) (n : ℕ) [NeZero n] (Y : Finset (TorusSite n)) :
    Measure (TorusField n × (Y → R.labels.Ω)) :=
  ((fieldHaar n).prod (Measure.pi fun _ : Y => R.labels.μ)).withDensity fun p =>
    open Classical in
    if IsHullState R.params (clusterRange R.coupling) p.1 Y then ENNReal.ofReal (R.labelWeight n p.1 Y p.2) else 0
def IntegrableOnStates (R : StepSetup) (n : ℕ) [NeZero n] (H : StateFunction R n) : Prop :=
  ∀ Y : Finset (TorusSite n),
    Integrable (fun p : TorusField n × (Y → R.labels.Ω) => H p.1 Y p.2) (stateMeasure R n Y)
def stateIntegralSum (R : StepSetup) (n : ℕ) [NeZero n] (H : StateFunction R n) : ℝ :=
  ∑ Y : Finset (TorusSite n), ∫ p : TorusField n × (Y → R.labels.Ω), H p.1 Y p.2 ∂(stateMeasure R n Y)
def conditionalCaseMean (R : StepSetup) {n : ℕ} [NeZero n] (g : StateFunction R (n * R.params.side))
    (ψ : TorusField (n * R.params.side) → BaseChoice R.params.side n → TorusField n → ℝ) (V : TorusField n)
    (Y : Finset (TorusSite n)) (ω : Y → CoarseLabel R.labels.Ω R.params.side) : ℝ :=
  caseMean R (hotCoreSites R V) V ⟨Y, ω⟩ fun W Yt ωt _ b => g W Yt ωt * ψ W b V
def stepMeanOfStatesStatement : Prop :=
  ∀ T : ParameterAssignment, T.Admissible → ∃ y₀ : ℝ, ∀ y : ℝ, y₀ ≤ y → ∀ R : StepSetup, R.OnParameters T y → R.IsWellPosed →
    ∀ (h : CoarseLabelFacts R) (lam x'' : ℝ) (n : ℕ) [NeZero n], IsBlockTorusSide R.params n →
      (∀ Yt : Finset (TorusSite (n * R.params.side)), IsFiniteMeasure (stateMeasure R (n * R.params.side) Yt)) →
      (∀ Y : Finset (TorusSite n), IsFiniteMeasure (stateMeasure (nextStepSetup R h lam x'') n Y)) ∧
      stateIntegralSum (nextStepSetup R h lam x'') n (fun _ _ _ => 1) =
        stateIntegralSum R (n * R.params.side) (fun _ _ _ => 1) ∧
      ∀ (g : StateFunction R (n * R.params.side))
        (ψ : TorusField (n * R.params.side) → BaseChoice R.params.side n → TorusField n → ℝ),
        IntegrableOnStates R (n * R.params.side) g →
        (∀ b, Measurable fun p : TorusField (n * R.params.side) × TorusField n => ψ p.1 b p.2) →
        (∃ C : ℝ, ∀ W b V, |ψ W b V| ≤ C) →
        IntegrableOnStates (nextStepSetup R h lam x'') n (conditionalCaseMean R g ψ) ∧
        stateIntegralSum (nextStepSetup R h lam x'') n (conditionalCaseMean R g ψ) =
          stateIntegralSum R (n * R.params.side) fun W Yt ωt => g W Yt ωt *
            ∑ b : BaseChoice R.params.side n,
              ∫ V, ψ W b V * stepTransitionDensity R.params R.coupling W b V ∂(fieldHaar n)
end ResponseInTheExpansion
end YangMills.Construction
end
