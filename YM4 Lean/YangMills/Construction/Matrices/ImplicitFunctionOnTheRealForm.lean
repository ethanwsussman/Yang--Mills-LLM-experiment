import YangMills.Construction.Matrices.RealAnalyticMapsOnSubspacesOfProducts
import Mathlib
set_option autoImplicit false
open Set
open scoped ContDiff Matrix.Norms.L2Operator
noncomputable section
namespace YangMills.Construction.Matrices.GroupLieProduct
namespace Subspaces
def RealForm.ImplicitFunctionStatement : Prop :=
  ∀ (S S' : Type) [Fintype S] [Fintype S'] (U : Set (S → ComplexMatrix2))
    (Φ : (S → ComplexMatrix2) → S' → ComplexMatrix2),
    (0 : S → ComplexMatrix2) ∈ U →
    IsAnalyticOnSubspace (hermitianTracelessFunctions S) (hermitianTracelessFunctions S') U Φ →
    Φ 0 = 0 →
    (∀ Y ∈ hermitianTracelessFunctions S', ∃ X ∈ hermitianTracelessFunctions S,
      deriv (fun t : ℝ => Φ (t • X)) 0 = Y) →
    ∃ (K C : Submodule ℝ (S → ComplexMatrix2)) (U₁ U₂ : Set (S → ComplexMatrix2))
      (f : (S → ComplexMatrix2) → S → ComplexMatrix2),
      K ⊔ C = hermitianTracelessFunctions S ∧ K ⊓ C = ⊥ ∧
      (∀ X, X ∈ K ↔ X ∈ hermitianTracelessFunctions S ∧ deriv (fun t : ℝ => Φ (t • X)) 0 = 0) ∧
      ComplexMatrix2.IsRelativelyOpen (K : Set (S → ComplexMatrix2)) U₁ ∧
      ComplexMatrix2.IsRelativelyOpen (C : Set (S → ComplexMatrix2)) U₂ ∧
      (0 : S → ComplexMatrix2) ∈ U₁ ∧ (0 : S → ComplexMatrix2) ∈ U₂ ∧
      (∀ X ∈ U₁, ∀ X' ∈ U₂, X + X' ∈ U ∧ (Φ (X + X') = 0 ↔ X' = f X)) ∧
      MapsTo f U₁ U₂ ∧ f 0 = 0 ∧
      IsAnalyticOnSubspace K C U₁ f ∧
      (∀ (d : ℕ) (j : (Fin d → ℝ) →L[ℝ] (S → ComplexMatrix2)), (∀ u, j u ∈ K) →
        ContDiffOn ℝ ∞ (f ∘ j) (j ⁻¹' U₁)) ∧
      ∀ X ∈ K, HasDerivAt (fun t : ℝ => f (t • X)) 0 0
end Subspaces
end YangMills.Construction.Matrices.GroupLieProduct
end
