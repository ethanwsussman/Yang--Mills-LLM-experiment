import YangMills.Construction.Matrices.GroupLieProducts
import Mathlib
set_option autoImplicit false
open Set
noncomputable section
namespace YangMills.Construction.Matrices.GroupLieProduct
def HolomorphicLinearComp : Prop :=
  ∀ (α τ : Type) [Fintype α] [Fintype τ] (b : Module.Basis (Fin 3) ℂ ComplexMatrix2.traceless)
    (N : Set (α → ComplexMatrix2)) (D : (α → ComplexMatrix2) → τ → ComplexMatrix2),
    (∀ ν : τ ≃ Fin (Fintype.card τ), IsHolomorphicOnTraceless b (matrixPiEquiv ν) N D) →
    ContinuousOn D N ∧
      ∀ (α' τ' : Type) [Fintype α'] [Fintype τ']
        (P : (α' → ComplexMatrix2) →ₗ[ℂ] (α → ComplexMatrix2))
        (Q : (τ → ComplexMatrix2) →ₗ[ℂ] (τ' → ComplexMatrix2)) (N' : Set (α' → ComplexMatrix2)),
        IsSupOpen N' → MapsTo P (tracelessPi α') (tracelessPi α) → MapsTo P N' N →
        ∀ ν' : τ' ≃ Fin (Fintype.card τ'),
          IsHolomorphicOnTraceless b (matrixPiEquiv ν') N' fun x => Q (D (P x))
end YangMills.Construction.Matrices.GroupLieProduct
end
