import YangMills.Construction.TwoPoints.TransformsOnTheLineAndTheirAlgebra
import Mathlib
set_option autoImplicit false
open MeasureTheory
open scoped NNReal
namespace YangMills.Construction.TwoPoints.SpectralMeasureUniqueness
open SpectralCalculus (SpectralPlane)
def Statement : Prop :=
  (∀ μ : ComplexMeasure SpectralPlane,
    (∀ t ∈ LineTransforms.dyadics, ∀ s : ℝ,
      SpectralCalculus.laplaceFourier μ t s = 0) → μ = 0) ∧
  ∀ μ ν : ComplexMeasure SpectralPlane,
    (∀ (t : ℝ≥0) (s : ℝ),
      SpectralCalculus.laplaceFourier μ t s = SpectralCalculus.laplaceFourier ν t s) → μ = ν
end YangMills.Construction.TwoPoints.SpectralMeasureUniqueness
