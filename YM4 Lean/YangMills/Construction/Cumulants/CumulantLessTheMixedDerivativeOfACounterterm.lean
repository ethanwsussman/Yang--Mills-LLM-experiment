import YangMills.Construction.Conventions.TorusBoundDefs
import YangMills.Construction.Functions.WeightedModulusSum
import YangMills.Construction.Lattice.WilsonGibbsMeasure
import YangMills.Construction.Probability.BoundedRealRandomVariable
import Mathlib
set_option autoImplicit false
open MeasureTheory
noncomputable section
namespace YangMills.Construction.Cumulants
def CumulantNearCountertermDeriv : Prop :=
  ∀ (n : ℕ) (w : WeightedModulusSum.Weights n) (Ω : Type) [MeasurableSpace Ω]
    (ν : Measure Ω) [IsProbabilityMeasure ν] (X : Fin n → Ω → ℝ)
    (ℰ : Coordinates.ComplexCoordinates n → ℂ) (Q : ℝ),
    (∀ i, Probability.IsBoundedRealRV (X i)) →
    ComplexVariables.IsHolomorphicScalar w.unitSet ℰ →
    ℰ 0 = 0 →
    (∀ z ∈ w.unitSet, ‖Complex.exp (-ℰ z) * momentGeneratingFunction ν X z‖ ≤ Q) →
    ‖mixedCumulant ν X - TorusBoundNotation.mixedDeriv ℰ 0‖ ≤
      Real.log 2 * (2 * Q + 2) ^ n * (n : ℝ) ^ n * ∏ i, w.c i
end YangMills.Construction.Cumulants
