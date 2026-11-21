import YangMills.Construction.InfiniteLattice.RationalPolynomialsInTheEntriesAndMeansOverBoxes
import YangMills.Construction.InfiniteLattice.StatesAtOneSpacing
import Mathlib
set_option autoImplicit false
open MeasureTheory Filter
open scoped Topology
noncomputable section
namespace YangMills.Construction.InfiniteLattice
variable {a : ℝ}
def realExpectation (ρ : GaugeFieldProbability a) (f : GaugeField a → ℝ) : ℝ :=
  ∫ U, f U ∂ρ.1
def statesInInterval (f : GaugeField a → ℝ) (p q : ℚ) : Set (GaugeFieldProbability a) :=
  {ρ | (p : ℝ) < realExpectation ρ f ∧ realExpectation ρ f < (q : ℝ)}
def rationalIntervalBasis (a : ℝ) : Set (Set (GaugeFieldProbability a)) :=
  {O | ∃ T : Set (Set (GaugeFieldProbability a)), T.Finite ∧
    (∀ O' ∈ T, ∃ f ∈ ratPolyObservables a, ∃ p q : ℚ, O' = statesInInterval f p q) ∧
    O = ⋂₀ T}
def RatPolyDense (a : ℝ) : Prop :=
  (ratPolyObservables a).Countable ∧
  (∀ f ∈ ratPolyObservables a,
    (fun U => (f U : ℂ)) ∈ continuousCylinderFunctions a) ∧
  (∀ q : ℚ, (fun _ => (q : ℝ)) ∈ ratPolyObservables a) ∧
  (∀ f ∈ ratPolyObservables a, ∀ g ∈ ratPolyObservables a,
    f + g ∈ ratPolyObservables a ∧ f * g ∈ ratPolyObservables a) ∧
  (∀ q : ℚ, ∀ f ∈ ratPolyObservables a,
    (q : ℝ) • f ∈ ratPolyObservables a) ∧
  (∀ f : GaugeField a → ℝ, Continuous f → ∀ ε : ℝ, 0 < ε →
    ∃ g ∈ ratPolyObservables a,
      observableSupNorm (fun U => ((f U - g U : ℝ) : ℂ)) ≤ ε) ∧
  ∀ f : GaugeField a → ℂ, Continuous f → ∀ ε : ℝ, 0 < ε →
    ∃ g ∈ complexRatPolyObservables a, observableSupNorm (f - g) ≤ ε
def RatPolyApproximatesInEveryState (a : ℝ) : Prop :=
  ∀ (ν : GaugeFieldProbability a) (f : GaugeField a → ℂ), IsBoundedObservable f →
    ∀ ε : ℝ, 0 < ε → ∃ ψ ∈ complexRatPolyObservables a,
      stateL2Norm ν (f - ψ) ≤ ε ∧ ∫ U, ‖f U - ψ U‖ ∂ν.1 ≤ ε
def RatPolyGeneratesStateBorel (a : ℝ) : Prop :=
  (∀ ν ν' : GaugeFieldProbability a,
    (∀ f ∈ ratPolyObservables a, realExpectation ν f = realExpectation ν' f) →
      ν = ν') ∧
  (rationalIntervalBasis a).Countable ∧
  TopologicalSpace.IsTopologicalBasis (rationalIntervalBasis a) ∧
  (inferInstance : MeasurableSpace (GaugeFieldProbability a)) =
    ⨆ f ∈ ratPolyObservables a,
      MeasurableSpace.comap (fun ρ : GaugeFieldProbability a => realExpectation ρ f)
        inferInstance ∧
  ∀ f : GaugeField a → ℂ, IsBoundedObservable f →
    Measurable fun ρ : GaugeFieldProbability a => ρ.expect f
def BoundedPointwiseClosureContainsObservables (a : ℝ) : Prop :=
  ∀ H : Submodule ℂ (GaugeField a → ℂ), (∀ f ∈ H, IsBoundedObservable f) →
    (∀ f ∈ continuousCylinderFunctions a, f ∈ H) →
    (∀ (f : ℕ → GaugeField a → ℂ) (g : GaugeField a → ℂ), (∀ n, f n ∈ H) →
      (∃ C : ℝ, ∀ n, observableSupNorm (f n) ≤ C) →
      (∀ U, Tendsto (fun n => f n U) atTop (𝓝 (g U))) → g ∈ H) →
    ∀ f : GaugeField a → ℂ, IsBoundedObservable f → f ∈ H
def RatPolyAndStateBorelSets : Prop :=
  ∀ L K : ℕ, Odd L → 13 ≤ L → 0 < K →
    RatPolyDense (PeriodicLattice.meshSize L (K : ℤ)) ∧
    RatPolyApproximatesInEveryState (PeriodicLattice.meshSize L (K : ℤ)) ∧
    RatPolyGeneratesStateBorel (PeriodicLattice.meshSize L (K : ℤ)) ∧
    BoundedPointwiseClosureContainsObservables (PeriodicLattice.meshSize L (K : ℤ))
end YangMills.Construction.InfiniteLattice
