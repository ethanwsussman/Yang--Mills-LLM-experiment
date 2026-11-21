import YangMills.Construction.Towers.GaussianIntegralsAndTheNormalisers
import Mathlib
set_option autoImplicit false
noncomputable section
namespace YangMills.Construction.LinearConstraint
def GaussianNumberByLevels : Prop :=
  ∀ (E C : Type) [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]
    [NormedAddCommGroup C] [InnerProductSpace ℝ C] [FiniteDimensional ℝ C]
    (Ω : Type) [Fintype Ω] [DecidableEq Ω] (lev : Ω → ℕ)
    (p : E →ₗ[ℝ] EuclideanSpace ℝ Ω) (q : E →ₗ[ℝ] C) (s : EuclideanSpace ℝ Ω →ₗ[ℝ] E)
    (j : C →ₗ[ℝ] E) (M : E →ₗ[ℝ] C) (T : QuadraticForm ℝ (LinearMap.ker M))
    (N N' A G : Matrix Ω Ω ℝ),
    (∀ ξ ξ' : E, inner ℝ ξ ξ' = inner ℝ (p ξ) (p ξ') + inner ℝ (q ξ) (q ξ')) →
    p ∘ₗ s = LinearMap.id → q ∘ₗ s = 0 → p ∘ₗ j = 0 → q ∘ₗ j = LinearMap.id →
    M ∘ₗ j = LinearMap.id →
    (∀ e e', lev e ≤ lev e' → N e e' = 0) →
    (∀ e e', lev e' ≤ lev e → N' e e' = 0) →
    A.det ≠ 0 → G.PosDef →
    (∀ (ξ : LinearMap.ker M) (y u : Ω → ℝ),
      WithLp.ofLp (p (ξ : E)) = y - Matrix.mulVec N y → y - Matrix.mulVec N' y = Matrix.mulVec A u →
      T ξ = dotProduct u (Matrix.mulVec G u)) →
    YangMills.Construction.GaussianConstraint.constrainedGaussianNumber M T =
      (2 * Real.pi) ^ ((Fintype.card Ω : ℝ) / 2) * G.det ^ (-(1 / 2) : ℝ) * |A.det|
end YangMills.Construction.LinearConstraint
end
