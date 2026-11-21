import YangMills.Construction.Matrices.GroupLieProducts
import Mathlib
set_option autoImplicit false
open scoped Matrix.Norms.L2Operator
noncomputable section
namespace YangMills.Construction.Matrices.GroupLieProduct
abbrev tracelessPiSubmodule (σ : Type) : Submodule ℂ (σ → ComplexMatrix2) :=
  Submodule.pi Set.univ fun _ => ComplexMatrix2.traceless
def HolomorphicOnTracelessIffDifferentiable : Prop :=
  ∀ (σ E : Type) [Fintype σ] [NormedAddCommGroup E] [NormedSpace ℂ E] [FiniteDimensional ℂ E]
    (l : ℕ) (b : Module.Basis (Fin 3) ℂ ComplexMatrix2.traceless)
    (e : E ≃ Coordinates.ComplexCoordinates l),
    IsLinearMap ℂ e → ∀ (O : Set (σ → ComplexMatrix2)) (f : (σ → ComplexMatrix2) → E),
      (IsHolomorphicOnTraceless b e O f ↔
        IsSupOpen O ∧
          DifferentiableOn ℂ (fun A : ↥(tracelessPiSubmodule σ) => f (A : σ → ComplexMatrix2))
            (Subtype.val ⁻¹' O))
end YangMills.Construction.Matrices.GroupLieProduct
end
