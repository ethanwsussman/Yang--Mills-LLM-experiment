import YangMills.Construction.ClusterExpansionOfAStep.FactorsOfAStep
import YangMills.Construction.ResponseInTheExpansion.ResponseOfAStep
import Mathlib
set_option autoImplicit false
noncomputable section
open MeasureTheory
namespace YangMills.Construction
open StepSettings TorusFields StepCosts
namespace WeightedResponses
def boundedCaseFunctionIntegrableStatement : Prop :=
  ∀ R : StepSetup, R.IsWellPosed → ∀ (n : ℕ) [NeZero n], R.params.n₀ ≤ n →
    ∀ (C : Finset (TorusSite n)) (V : TorusField n) (q : CoarseState R n),
    coarseStateMass R C V q ≠ ⊤ → ∀ (F : CaseFunction R n) (K : ℝ),
    (∀ (Yt : Finset (TorusSite (n * R.params.side))) (bad : Finset (TorusBond (n * R.params.side)))
      (b : BaseChoice R.params.side n),
      Measurable fun p : TorusField (n * R.params.side) × (Yt → R.labels.Ω) => F p.1 Yt p.2 bad b) →
    (∀ W Yt ωt bad b, |F W Yt ωt bad b| ≤ K) → CaseIntegrable R C V q F
end WeightedResponses
end YangMills.Construction
end
