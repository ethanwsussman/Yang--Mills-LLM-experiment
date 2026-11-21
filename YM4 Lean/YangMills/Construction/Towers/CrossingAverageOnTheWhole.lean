import YangMills.Construction.PeriodicOperators.QuotientsTransposesAndNorm
import YangMills.Construction.Towers.ExponentialConjugatesOfKernelsAndMaps
import Mathlib
set_option autoImplicit false
noncomputable section
namespace YangMills.Construction.Tower
open PeriodicOperators (colourEdges applyKernel wOpNorm OpNormSummable)
open PeriodicOperators.Quotients (MapsFiniteNorm finiteNormSpace)
namespace CrossingSmoothingBound
def conjKernel (L k i : ℕ) (θ : InfiniteLattice.AmbientSpace) :
    (colourEdges L k (i + 1)).Carrier → (colourEdges L k i).Carrier → ℂ :=
  expConjOfMap (IndexedEvaluation.edgeForms L k i) (IndexedEvaluation.edgeForms L k (i + 1)) θ
    fun v => (L : ℝ)⁻¹ • FullSpace.crossingSmoothing L
      (a := meshAt L k (i + 1)) (a' := meshAt L k i) v
def NormBound : Prop :=
  ∀ L : ℕ, Conventions.IsAdmissibleBlockingFactor L → ∀ k i : ℕ, i + 1 ≤ k →
    ∀ θ : InfiniteLattice.AmbientSpace,
    MapsFiniteNorm (colourEdges L k i) (colourEdges L k (i + 1)) (conjKernel L k i θ) ∧
    OpNormSummable (colourEdges L k i).weightOf (colourEdges L k (i + 1)).weightOf
      (finiteNormSpace (colourEdges L k i)) (applyKernel (conjKernel L k i θ)) ∧
    wOpNorm (colourEdges L k i).weightOf (colourEdges L k (i + 1)).weightOf
      (finiteNormSpace (colourEdges L k i)) (applyKernel (conjKernel L k i θ)) ≤
      ENNReal.ofReal (Real.exp (2 * TorusMetric.l1NormVec θ * meshAt L k (i + 1)))
end CrossingSmoothingBound
end YangMills.Construction.Tower
end
