import YangMills.Construction.PeriodicOperators.QuotientsTransposesAndNorm
import YangMills.Construction.PeriodicOperators.SymbolMatricesAndPlaneWaves
import YangMills.Construction.Towers.TheScaledPicture
import Mathlib
set_option autoImplicit false
noncomputable section
namespace YangMills.Construction.Tower
open PeriodicOperators (colourEdges expConj applyKernel wOpNorm OpNormSummable)
open PeriodicOperators.Quotients (MapsFiniteNorm finiteNormSpace)
namespace RescaledQFullSpace
def conjugate (L k : ℕ) (θ : InfiniteLattice.AmbientSpace) :
    (colourEdges L k k).Carrier → (colourEdges L k 0).Carrier → ℂ :=
  expConj (colourEdges L k 0) (colourEdges L k k) θ
    (FullSpace.rescaledOperators L k fun _ => 1).Q
def OpNormLeExp : Prop :=
  ∀ L : ℕ, Conventions.IsAdmissibleBlockingFactor L → ∀ k : ℕ, 1 ≤ k →
    ∀ θ : InfiniteLattice.AmbientSpace,
    MapsFiniteNorm (colourEdges L k 0) (colourEdges L k k) (conjugate L k θ) ∧
    OpNormSummable (colourEdges L k 0).weightOf (colourEdges L k k).weightOf
      (finiteNormSpace (colourEdges L k 0)) (applyKernel (conjugate L k θ)) ∧
    wOpNorm (colourEdges L k 0).weightOf (colourEdges L k k).weightOf
      (finiteNormSpace (colourEdges L k 0)) (applyKernel (conjugate L k θ)) ≤
      ENNReal.ofReal (Real.exp (2 * TorusMetric.l1NormVec θ))
end RescaledQFullSpace
end YangMills.Construction.Tower
end
