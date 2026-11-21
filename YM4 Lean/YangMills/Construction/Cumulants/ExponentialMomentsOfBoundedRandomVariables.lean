import YangMills.Construction.Coordinates.HolomorphyInCoordinates
import YangMills.Construction.Probability.BoundedRealRandomVariable
import Mathlib
set_option autoImplicit false
open MeasureTheory
noncomputable section
namespace YangMills.Construction.Cumulants.ExpMoments
def expMomentFn {Ω : Type*} [MeasurableSpace Ω] (μ : Measure Ω) {n : ℕ}
    (X : Fin n → Ω → ℝ) (z : Coordinates.ComplexCoordinates n) : ℂ :=
  ∫ ω, Complex.exp (∑ i, z i * (X i ω : ℂ)) ∂μ
def HolomorphicAndNormalized : Prop :=
  ∀ (Ω : Type) [MeasurableSpace Ω] (μ : Measure Ω) [IsProbabilityMeasure μ] (n : ℕ), 1 ≤ n →
    ∀ X : Fin n → Ω → ℝ, (∀ i, Probability.IsBoundedRealRV (X i)) →
      Coordinates.ComplexCoordinates.IsHolomorphicIn (N' := 1) Set.univ
          (fun z _ => expMomentFn μ X z) ∧
        expMomentFn μ X 0 = 1
end YangMills.Construction.Cumulants.ExpMoments
end
