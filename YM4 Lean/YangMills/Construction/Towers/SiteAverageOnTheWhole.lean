import YangMills.Construction.PeriodicOperators.QuotientsTransposesAndNorm
import YangMills.Construction.Towers.ExponentialConjugatesOfKernelsAndMaps
import Mathlib
set_option autoImplicit false
noncomputable section
namespace YangMills.Construction.Tower.FullVertexSmoothing
def conjugateKernel (L k i : ℕ) (θ : InfiniteLattice.AmbientSpace) :
    (PeriodicOperators.colourVertices L k (i + 1)).Carrier →
      (PeriodicOperators.colourVertices L k i).Carrier → ℂ :=
  expConjOfMap (IndexedEvaluation.vertices L k i) (IndexedEvaluation.vertices L k (i + 1)) θ
    (FullSpace.vertexSmoothing L (a := meshAt L k (i + 1)) (a' := meshAt L k i))
def Claim : Prop :=
  ∀ L : ℕ, Conventions.IsAdmissibleBlockingFactor L → ∀ k i : ℕ, i + 1 ≤ k →
    ∀ θ : InfiniteLattice.AmbientSpace,
    PeriodicOperators.Quotients.MapsFiniteNorm (PeriodicOperators.colourVertices L k i)
      (PeriodicOperators.colourVertices L k (i + 1)) (conjugateKernel L k i θ) ∧
    PeriodicOperators.OpNormSummable (PeriodicOperators.colourVertices L k i).weightOf
      (PeriodicOperators.colourVertices L k (i + 1)).weightOf
      (PeriodicOperators.Quotients.finiteNormSpace (PeriodicOperators.colourVertices L k i))
      (PeriodicOperators.applyKernel (conjugateKernel L k i θ)) ∧
    PeriodicOperators.wOpNorm (PeriodicOperators.colourVertices L k i).weightOf
      (PeriodicOperators.colourVertices L k (i + 1)).weightOf
      (PeriodicOperators.Quotients.finiteNormSpace (PeriodicOperators.colourVertices L k i))
      (PeriodicOperators.applyKernel (conjugateKernel L k i θ)) ≤
      ENNReal.ofReal (Real.exp (TorusMetric.l1NormVec θ * meshAt L k (i + 1)))
end YangMills.Construction.Tower.FullVertexSmoothing
end
