import YangMills.Construction.Towers.GaussianIntegralsAndTheNormalisers
import Mathlib
set_option autoImplicit false
noncomputable section
namespace YangMills.Construction.GaussianConstraint
def SaddleDeterminantIdentity : Prop :=
  ∀ (E F : Type) [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]
    [NormedAddCommGroup F] [InnerProductSpace ℝ F] [FiniteDimensional ℝ F]
    (M : E →ₗ[ℝ] F) (T : QuadraticForm ℝ (LinearMap.ker M)),
    Function.Surjective M → T.PosDef →
    ∀ X : E →ₗ[ℝ] E, X.IsSymmetric →
      (∀ w : LinearMap.ker M, inner ℝ (w : E) (X w) = T w) →
      constrainedGaussianNumber M T =
          (2 * Real.pi) ^ (((Module.finrank ℝ E : ℝ) - (Module.finrank ℝ F : ℝ)) / 2) *
            |LinearMap.det (saddlePointOperator X M)| ^ (-(1 / 2) : ℝ) ∧
        ((∀ w : E, w ≠ 0 → 0 < inner ℝ w (X w)) →
          |LinearMap.det (saddlePointOperator X M)| =
            LinearMap.det X *
              LinearMap.det (M ∘ₗ (Ring.inverse X : E →ₗ[ℝ] E) ∘ₗ LinearMap.adjoint M))
end YangMills.Construction.GaussianConstraint
end
