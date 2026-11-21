import YangMills.Construction.RunningCouplingSlope.VolumeFactorsOfLinearMaps
import YangMills.Construction.Towers.GaussianIntegralsAndTheNormalisers
import Mathlib
set_option autoImplicit false
noncomputable section
namespace YangMills.Construction.LinearConstraint
def borderedBlockOperator {E F : Type*} [AddCommGroup E] [Module ℝ E] [AddCommGroup F] [Module ℝ F]
    (m : E →ₗ[ℝ] E) (s : F →ₗ[ℝ] E) (t : E →ₗ[ℝ] F) : (E × F) →ₗ[ℝ] E × F :=
  (m.coprod s).prod (t ∘ₗ LinearMap.fst ℝ E F)
def GaussianNumberViaBorderedDeterminant : Prop :=
  ∀ (E V F W Y : Type)
    [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]
    [NormedAddCommGroup V] [InnerProductSpace ℝ V] [FiniteDimensional ℝ V]
    [NormedAddCommGroup F] [InnerProductSpace ℝ F] [FiniteDimensional ℝ F]
    [NormedAddCommGroup W] [InnerProductSpace ℝ W] [FiniteDimensional ℝ W]
    [NormedAddCommGroup Y] [InnerProductSpace ℝ Y] [FiniteDimensional ℝ Y]
    (D : E →ₗ[ℝ] V) (Dc : F →ₗ[ℝ] W) (Q : V →ₗ[ℝ] W) (r r₂ : E →ₗ[ℝ] F) (n : V →ₗ[ℝ] F)
    (p : V →ₗ[ℝ] E) (b : ℝ) (T : QuadraticForm ℝ (LinearMap.ker Q)) (X : V →ₗ[ℝ] V)
    (l : V →ₗ[ℝ] Y),
    Function.Surjective Q →
    r ∘ₗ LinearMap.adjoint r = LinearMap.id →
    Q ∘ₗ D = Dc ∘ₗ r →
    0 < b →
    (r + n ∘ₗ D) ∘ₗ LinearMap.adjoint (r + n ∘ₗ D) = b • LinearMap.id →
    (r + n ∘ₗ D) ∘ₗ LinearMap.adjoint r = b • LinearMap.id →
    r₂ ∘ₗ LinearMap.adjoint r₂ = b • LinearMap.id →
    Function.Injective (D ∘ₗ (LinearMap.ker r).subtype) →
    (∀ ξ, 0 ≤ T ξ) →
    (∀ ξ : LinearMap.ker Q, T ξ = 0 ↔ (ξ : V) ∈ (LinearMap.ker r).map D) →
    LinearMap.det (borderedBlockOperator (p ∘ₗ D) (LinearMap.adjoint r₂) (r + n ∘ₗ D)) ≠ 0 →
    X.IsSymmetric →
    (∀ ξ : V, (Q + Dc ∘ₗ n) ξ = 0 →
      ∀ h : ξ + D (LinearMap.adjoint r (n ξ)) ∈ LinearMap.ker Q,
        inner ℝ ξ (X ξ) = T ⟨_, h⟩ +
          ‖p ξ - b⁻¹ • LinearMap.adjoint r₂ (r₂ (p ξ))‖ ^ 2) →
    Function.Bijective (l ∘ₗ D ∘ₗ (LinearMap.ker r).subtype) →
    LinearMap.det (GaussianConstraint.saddlePointOperator X (Q + Dc ∘ₗ n)) ≠ 0 ∧
      GaussianConstraint.constrainedGaussianNumber Q (T + (normSqForm l).comp (LinearMap.ker Q).subtype) *
          absDetOfMap (l ∘ₗ D ∘ₗ (LinearMap.ker r).subtype) =
        (b ^ Module.finrank ℝ F) ^ (1 / 2 : ℝ) * (b ^ Module.finrank ℝ F)⁻¹ *
          (2 * Real.pi) ^ (((Module.finrank ℝ V : ℝ) - (Module.finrank ℝ W : ℝ)) / 2) *
          |LinearMap.det (GaussianConstraint.saddlePointOperator X (Q + Dc ∘ₗ n))| ^ (-(1 / 2) : ℝ) *
          |LinearMap.det (borderedBlockOperator (p ∘ₗ D) (LinearMap.adjoint r₂) (r + n ∘ₗ D))|
end YangMills.Construction.LinearConstraint
end
