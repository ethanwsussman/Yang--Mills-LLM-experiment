import YangMills.Construction.EuclideanSpectral.ProjMeasureBasicFacts
import Mathlib
set_option autoImplicit false
noncomputable section
namespace YangMills.Construction.EuclideanSpectral
namespace ProjMeasure
variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H] {n : ℕ}
  [NeZero n]
def boundedIntegral (E : ProjMeasure H n) (f : EuclideanSpace ℝ (Fin n) → ℂ) : H →ₗ[ℂ] H :=
  Classical.epsilon (E.IsWeakIntegralOp f)
def boundedIntegralOn (E : ProjMeasure H n) (B : BorelSubset n)
    (f : EuclideanSpace ℝ (Fin n) → ℂ) : H →ₗ[ℂ] H :=
  E.boundedIntegral (B.1.indicator f)
end ProjMeasure
end YangMills.Construction.EuclideanSpectral
