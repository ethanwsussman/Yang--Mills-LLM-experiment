import Reconstruction.MinkowskiSpace.VectorsAtRealPointsDefs
import Mathlib
set_option autoImplicit false
open Filter MeasureTheory
open scoped ComplexConjugate InnerProductSpace Topology
noncomputable section
namespace YangMills.Construction.RealPointVectors
def TensorTimeDerivBound : Prop :=
  ∀ (k n : ℕ) (u : Fin (n + 1) → (Fin 4 → ℝ) → ℂ),
    (∀ i, u i ∈ WightmanTheory.schwartzR4) →
      RealPointVectors.maxTimeDerivL1 k (TestSpaces.tensorProd u) ≤
        ((n + 1 : ℕ) : ℝ) ^ (2 * k) * ∏ i, RealPointVectors.maxPartialL1 k (u i)
end YangMills.Construction.RealPointVectors
