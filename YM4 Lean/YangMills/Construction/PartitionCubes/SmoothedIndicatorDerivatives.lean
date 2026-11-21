import YangMills.Construction.PartitionCubes.CubesAndCutoffs
import Mathlib
set_option autoImplicit false
open MeasureTheory
open scoped ContDiff
noncomputable section
namespace YangMills.Construction.PartitionCubes
def SmoothedIndicatorDerivBounds : Prop :=
  ∃ C₀ : ℝ, ∀ (𝒮 : RegionSequence.NestedRegions) (r : ℝ), 0 < r →
    ∀ A : Set 𝒮.Point, MeasurableSet[borel 𝒮.Point] A →
      (∀ x, 0 ≤ smoothedIndicator r A x) ∧
      (∀ x, smoothedIndicator r A x ≤ 1) ∧
      ContDiff ℝ ∞ (fun p : Fin 4 → ℝ =>
        smoothedIndicator r A (Torus.torusProj 4 𝒮.side p)) ∧
      ∀ i ≤ 2, ∀ (μ : Fin i → Fin 4) (p : Fin 4 → ℝ),
        |iteratedFDeriv ℝ i (fun p : Fin 4 → ℝ =>
            smoothedIndicator r A (Torus.torusProj 4 𝒮.side p)) p
          fun k => Pi.single (μ k) 1| ≤ C₀ * r⁻¹ ^ i
end YangMills.Construction.PartitionCubes
