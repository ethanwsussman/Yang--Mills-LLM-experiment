import YangMills.Construction.Continuum.FunctionsNormsBallsAndNeighbourhoods
import Mathlib
set_option autoImplicit false
open scoped ENNReal NNReal
noncomputable section
namespace YangMills.Construction.TorusTransport
def realC1Compact : Set (RealFun (Fin 4 → ℝ)) :=
  {f | f.toComplex ∈ c1CompactSupport}
def gradR4 (f : RealFun (Fin 4 → ℝ)) (x : Fin 4 → ℝ) : Fin 4 → ℝ :=
  fun μ => TestFunctions.partialDerivR4 μ f x
theorem gradNorm_euclidean_eq (D : TransportData) (f : RealFun (Fin 4 → ℝ)) (x : Fin 4 → ℝ) :
    Domain.euclidean.gradNorm D f x = euclidNorm (gradR4 f x) := by
  simp [Domain.gradNorm, Domain.partialDeriv, gradR4,
    TorusMetric.euclidNormVec, Real.norm_eq_abs, sq_abs]
def gradOscillation (f : realC1Compact) (δ : ℝ≥0) : ℝ≥0∞ :=
  ⨆ (x : Fin 4 → ℝ) (y : Fin 4 → ℝ) (_ : euclidNorm (x - y) ≤ δ),
    ENNReal.ofReal (euclidNorm (gradR4 f.1 x - gradR4 f.1 y))
def TransportData.translationModulus (D : TransportData) (f : realC1Compact) (δ : ℝ≥0) : ℝ≥0∞ :=
  max (Domain.euclidean.gradSupNorm D f.1 * δ)
    (ENNReal.ofReal (40 * D.M) * gradOscillation f δ)
end YangMills.Construction.TorusTransport
end
