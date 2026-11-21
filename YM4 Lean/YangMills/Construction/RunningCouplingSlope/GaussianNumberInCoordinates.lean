import YangMills.Construction.RunningCouplingSlope.VolumeFactorsOfLinearMaps
import YangMills.Construction.Towers.GaussianIntegralsAndTheNormalisers
import Mathlib
set_option autoImplicit false
noncomputable section
namespace YangMills.Construction.LinearConstraint
def GaussianNumberCoordinateFormula : Prop :=
  ∀ (E E₁ C : Type) [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]
    [NormedAddCommGroup E₁] [InnerProductSpace ℝ E₁] [FiniteDimensional ℝ E₁]
    [NormedAddCommGroup C] [InnerProductSpace ℝ C] [FiniteDimensional ℝ C]
    (Ω : Type) [Fintype Ω] [DecidableEq Ω]
    (p : E →ₗ[ℝ] E₁) (q : E →ₗ[ℝ] C) (s : E₁ →ₗ[ℝ] E) (j : C →ₗ[ℝ] E) (M : E →ₗ[ℝ] C)
    (T : QuadraticForm ℝ (LinearMap.ker M))
    (Ψ : EuclideanSpace ℝ Ω →ₗ[ℝ] LinearMap.ker M) (G : Matrix Ω Ω ℝ),
    (∀ ξ ξ' : E, inner ℝ ξ ξ' = inner ℝ (p ξ) (p ξ') + inner ℝ (q ξ) (q ξ')) →
    p ∘ₗ s = LinearMap.id → q ∘ₗ s = 0 → p ∘ₗ j = 0 → q ∘ₗ j = LinearMap.id →
    M ∘ₗ j = LinearMap.id →
    G.PosDef →
    Function.Bijective (p ∘ₗ (LinearMap.ker M).subtype ∘ₗ Ψ) →
    (∀ u, T (Ψ u) = dotProduct (WithLp.ofLp u) (Matrix.mulVec G (WithLp.ofLp u))) →
    YangMills.Construction.GaussianConstraint.constrainedGaussianNumber M T =
      (2 * Real.pi) ^ ((Fintype.card Ω : ℝ) / 2) * G.det ^ (-(1 / 2) : ℝ) *
        YangMills.Construction.LinearConstraint.absDetOfMap (p ∘ₗ (LinearMap.ker M).subtype ∘ₗ Ψ)
end YangMills.Construction.LinearConstraint
end
