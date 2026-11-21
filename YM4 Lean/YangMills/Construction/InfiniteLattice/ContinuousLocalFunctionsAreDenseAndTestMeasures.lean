import YangMills.Construction.InfiniteLattice.ObservablesHypercubicLatticeMapsAndHyperplanes
import YangMills.Construction.InfiniteLattice.SignsAndWeakConvergenceAtSpacingOne
import YangMills.Construction.InfiniteLattice.SpecificationGaugeTransformationsAndClassesOfMeasures
import Mathlib
set_option autoImplicit false
open MeasureTheory Filter
open scoped Topology
noncomputable section
namespace YangMills.Construction
namespace InfiniteLattice
def ContinuousLocalDensity.Statement : Prop :=
  ∀ (ν : Measure (GaugeField 1)) [IsProbabilityMeasure ν],
    (∀ (S : Set AmbientSpace), ∀ F ∈ regionObservables 1 S, ∃ G : ℕ → GaugeField 1 → ℂ,
      (∀ k, 1 ≤ k → G k ∈ regionObservables 1 S ∩ continuousLocalFunctions 1) ∧
      Tendsto (fun k => stateEval ν fun U => ‖G k U - F U‖ ^ 2) atTop (𝓝 (0 : ℝ))) ∧
    (∀ (ν' : Measure (GaugeField 1)) [IsProbabilityMeasure ν'],
      (∀ F ∈ continuousLocalFunctions 1, stateEval ν' F = stateEval ν F) → ν' = ν) ∧
    (∀ r : LatticeSymmetry 1,
      Continuous r.pullbackField ∧
      (∀ F ∈ continuousLocalFunctions 1, r.actOn F ∈ continuousLocalFunctions 1) ∧
      ((∀ F ∈ continuousLocalFunctions 1, stateEval ν (r.actOn F) = stateEval ν F) →
        IsSymmetricUnder ν r)) ∧
    (∀ μ : ℕ → Measure (GaugeField 1), (∀ k, 1 ≤ k → IsProbabilityMeasure (μ k)) →
      ∀ κ : ℕ → ℕ, (∀ j, 1 ≤ j → 1 ≤ κ j) → (∀ i j, 1 ≤ i → i < j → κ i < κ j) →
        WeakConvergesUnitSpacing (fun j => μ (κ j)) ν →
          IsWeakClusterPointUnitSpacing μ ν)
end InfiniteLattice
end YangMills.Construction
