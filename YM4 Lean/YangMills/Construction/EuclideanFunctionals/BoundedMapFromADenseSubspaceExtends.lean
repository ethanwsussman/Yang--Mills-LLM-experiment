import YangMills.Construction.EuclideanFunctionals.SymmetricEuclideanFunctionalWithReconstruction
import Mathlib
set_option autoImplicit false
noncomputable section
namespace YangMills.Construction.EuclideanFunctionals.DenseExtension
def DenseExtensionTheorem : Prop :=
  ∀ (m : SharpScale) (S : ConnFamily) (σ : EuclidFunctionalWithRecon m S)
    (D₀ : Submodule ℂ σ.space) (b : ℝ) (Z₀ : D₀ →ₗ[ℂ] σ.space),
    Dense (D₀ : Set σ.space) → 0 ≤ b →
    (∀ ψ : D₀, ‖Z₀ ψ‖ ≤ b * ‖(ψ : σ.space)‖) →
    ∃ Z : σ.space →L[ℂ] σ.space,
      (∀ ψ : D₀, Z ψ = Z₀ ψ) ∧
      (∀ Z' : σ.space →L[ℂ] σ.space, (∀ ψ : D₀, Z' ψ = Z₀ ψ) → Z' = Z) ∧
      ‖Z‖ ≤ b
end YangMills.Construction.EuclideanFunctionals.DenseExtension
