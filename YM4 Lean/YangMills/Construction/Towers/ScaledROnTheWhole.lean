import YangMills.Construction.PeriodicOperators.QuotientsTransposesAndNorm
import YangMills.Construction.PeriodicOperators.SymbolMatricesAndPlaneWaves
import YangMills.Construction.Towers.TheScaledPicture
import Mathlib
set_option autoImplicit false
noncomputable section
namespace YangMills.Construction.Tower
open YangMills.Construction.PeriodicOperators (colourVertices expConj applyKernel wOpNorm
  OpNormSummable)
open YangMills.Construction.PeriodicOperators.Quotients (MapsFiniteNorm finiteNormSpace)
namespace WholeLatticeR
def conjugatedKernel (L k : ℕ) (θ : InfiniteLattice.AmbientSpace) :
    (colourVertices L k k).Carrier → (colourVertices L k 0).Carrier → ℂ :=
  expConj (colourVertices L k 0) (colourVertices L k k) θ
    (FullSpace.rescaledOperators L k fun _ => 1).R
def ConjugateBound : Prop :=
  ∀ L : ℕ, Conventions.IsAdmissibleBlockingFactor L → ∀ k : ℕ, 1 ≤ k →
    ∀ θ : InfiniteLattice.AmbientSpace,
    MapsFiniteNorm (colourVertices L k 0) (colourVertices L k k) (conjugatedKernel L k θ) ∧
    OpNormSummable (colourVertices L k 0).weightOf (colourVertices L k k).weightOf
      (finiteNormSpace (colourVertices L k 0)) (applyKernel (conjugatedKernel L k θ)) ∧
    wOpNorm (colourVertices L k 0).weightOf (colourVertices L k k).weightOf
      (finiteNormSpace (colourVertices L k 0)) (applyKernel (conjugatedKernel L k θ)) ≤
      ENNReal.ofReal (Real.exp (TorusMetric.l1NormVec θ))
end WholeLatticeR
end YangMills.Construction.Tower
end
