import YangMills.Construction.Towers.GaussianIntegralsAndTheNormalisers
import Mathlib
set_option autoImplicit false
noncomputable section
namespace YangMills.Construction.Tower
def ConstrainedGaussianIsometryInvariance : Prop :=
  ∀ (L n k i i' L₂ n₂ k₂ l l' : ℕ) (O : edgeFormSpace L n k i ≃ₗ[ℝ] edgeFormSpace L₂ n₂ k₂ l)
    (O' : edgeFormSpace L n k i' ≃ₗ[ℝ] edgeFormSpace L₂ n₂ k₂ l'),
    (∀ B B' : edgeFormSpace L n k i,
      (edgeFormPairing (O B : Edge L₂ n₂ k₂ l → Matrices.ComplexMatrix2) (O B')).re =
        (edgeFormPairing (B : Edge L n k i → Matrices.ComplexMatrix2) B').re) →
    (∀ B B' : edgeFormSpace L n k i',
      (edgeFormPairing (O' B : Edge L₂ n₂ k₂ l' → Matrices.ComplexMatrix2) (O' B')).re =
        (edgeFormPairing (B : Edge L n k i' → Matrices.ComplexMatrix2) B').re) →
    ∀ (M : edgeFormSpace L n k i →ₗ[ℝ] edgeFormSpace L n k i')
      (M' : edgeFormSpace L₂ n₂ k₂ l →ₗ[ℝ] edgeFormSpace L₂ n₂ k₂ l'),
      (∀ B, M' (O B) = O' (M B)) →
      ∀ (T : QuadraticForm ℝ (LinearMap.ker M)) (T' : QuadraticForm ℝ (LinearMap.ker M')),
        (∀ (B : LinearMap.ker M) (B' : LinearMap.ker M'), B'.1 = O B.1 → T' B' = T B) →
        constrainedGaussianOnEdgeForms M' T' = constrainedGaussianOnEdgeForms M T
end YangMills.Construction.Tower
end
