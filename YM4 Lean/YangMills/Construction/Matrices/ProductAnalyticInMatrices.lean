import YangMills.Construction.Matrices.GroupLieProducts
import Mathlib
set_option autoImplicit false
open Set Filter
open scoped Topology Matrix.Norms.L2Operator
noncomputable section
namespace YangMills.Construction.Matrices.GroupLieProduct
variable {ι κ : Type}
def IsMatrixAnalyticAt [Fintype ι] [Fintype κ] (W : Set (ι ⊕ κ → ComplexMatrix2))
    (Φ : (ι ⊕ κ → ComplexMatrix2) → ComplexMatrix2) (p : ι ⊕ κ → ComplexMatrix2) : Prop :=
  ∃ F : (ι ⊕ κ → ComplexMatrix2) → ComplexMatrix2, AnalyticAt ℂ F p ∧ ∀ᶠ w in 𝓝 p, w ∈ W → Φ w = F w
def HolomorphicMatrixAnalyticity : Prop :=
  ∀ (ι κ : Type) [Fintype ι] [Fintype κ] (b : Module.Basis (Fin 3) ℂ ComplexMatrix2.traceless)
    (W : Set (ι ⊕ κ → ComplexMatrix2)) (Φ : (ι ⊕ κ → ComplexMatrix2) → ComplexMatrix2),
    (IsHolomorphicToCoords b Coordinates.ComplexCoordinates.matrixEquiv W Φ ∨
      IsHolomorphicToUnimodular b W Φ) →
    ∀ p ∈ W, IsMatrixAnalyticAt W Φ p
end YangMills.Construction.Matrices.GroupLieProduct
end
