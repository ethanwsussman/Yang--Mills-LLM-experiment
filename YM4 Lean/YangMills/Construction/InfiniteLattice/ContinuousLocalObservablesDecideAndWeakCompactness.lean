import YangMills.Construction.InfiniteLattice.SignsAndWeakConvergenceAtSpacingOne
import YangMills.Construction.InfiniteLattice.SpecificationGaugeTransformationsAndClassesOfMeasures
import Mathlib
set_option autoImplicit false
open MeasureTheory
noncomputable section
namespace YangMills.Construction.InfiniteLattice
def LocalDeterminationAndCompactness : Prop :=
  (∃ 𝒟 : Set (GaugeField 1 → ℂ), 𝒟.Countable ∧ 𝒟 ⊆ continuousLocalFunctions 1 ∧
    ∀ F : GaugeField 1 → ℂ, Continuous F →
      ∀ ε : ℝ, 0 < ε → ∃ H ∈ 𝒟, observableSupNorm (F - H) < ε) ∧
  (∀ (ν ν' : Measure (GaugeField 1)) [IsProbabilityMeasure ν] [IsProbabilityMeasure ν'],
    (∀ F ∈ continuousLocalFunctions 1, stateEval ν F = stateEval ν' F) → ν = ν') ∧
  (∀ μ : ℕ → Measure (GaugeField 1), (∀ k, 1 ≤ k → IsProbabilityMeasure (μ k)) →
    ∃ (κ : ℕ → ℕ) (ν : Measure (GaugeField 1)), IsProbabilityMeasure ν ∧
      (∀ j, 1 ≤ j → 1 ≤ κ j) ∧ (∀ i j, 1 ≤ i → i < j → κ i < κ j) ∧
      WeakConvergesUnitSpacing (fun j => μ (κ j)) ν) ∧
  (∀ r : LatticeSymmetry 1,
    (∀ (ν : Measure (GaugeField 1)) [IsProbabilityMeasure ν],
      (∀ F ∈ continuousLocalFunctions 1, stateEval ν (r.actOn F) = stateEval ν F) →
        IsSymmetricUnder ν r) ∧
    (∀ (μ : ℕ → Measure (GaugeField 1)) (ν : Measure (GaugeField 1)),
      (∀ k, 1 ≤ k → IsProbabilityMeasure (μ k)) → IsProbabilityMeasure ν →
        WeakConvergesUnitSpacing μ ν → (∀ k, 1 ≤ k → IsSymmetricUnder (μ k) r) →
          IsSymmetricUnder ν r))
end YangMills.Construction.InfiniteLattice
