import YangMills.Construction.Towers.ChangeOfTheGaugeFixingAndOfTheConstraint
import Mathlib
set_option autoImplicit false
noncomputable section
namespace YangMills.Construction.GaussianConstraint
def GaussianNumberViaTwoSaddleDeterminants : Prop :=
  ∀ (A C G Gc : Type) [NormedAddCommGroup A] [InnerProductSpace ℝ A] [FiniteDimensional ℝ A]
    [NormedAddCommGroup C] [InnerProductSpace ℝ C] [FiniteDimensional ℝ C]
    [NormedAddCommGroup G] [InnerProductSpace ℝ G] [FiniteDimensional ℝ G]
    [NormedAddCommGroup Gc] [InnerProductSpace ℝ Gc] [FiniteDimensional ℝ Gc]
    (D : G →ₗ[ℝ] A) (Dc : Gc →ₗ[ℝ] C) (Q : A →ₗ[ℝ] C) (r : G →ₗ[ℝ] Gc) (ν : A →ₗ[ℝ] Gc) (a : ℝ)
    (H T : QuadraticForm ℝ (LinearMap.ker Q)) (Λ : LinearMap.ker Q →ₗ[ℝ] LinearMap.ker r)
    (v : LinearMap.ker r →ₗ[ℝ] LinearMap.ker r) (X : A →ₗ[ℝ] A),
    Function.Injective D → Function.Injective Dc →
    Function.Surjective Q → Function.Surjective r →
    Q ∘ₗ D = Dc ∘ₗ r → r ∘ₗ LinearMap.adjoint r = LinearMap.id →
    0 < a →
    shiftedGaugeMap r ν D ∘ₗ LinearMap.adjoint (shiftedGaugeMap r ν D) = a • LinearMap.id →
    (∀ (B : LinearMap.ker Q) (κ : LinearMap.ker r) (hκ : D κ ∈ LinearMap.ker Q),
      H (B + ⟨D κ, hκ⟩) = H B) →
    (∀ B : LinearMap.ker Q, T B = H B + ‖Λ B‖ ^ 2) → T.PosDef →
    (∀ (κ : LinearMap.ker r) (hκ : D κ ∈ LinearMap.ker Q), v κ = Λ ⟨D κ, hκ⟩) →
    |LinearMap.det v| = 1 →
    X.IsSymmetric →
    (∀ B : A, shiftedConstraint Q Dc ν B = 0 →
      ∀ hB : B + D (LinearMap.adjoint r (ν B)) ∈ LinearMap.ker Q,
        inner ℝ B (X B) = H ⟨_, hB⟩ + ‖LinearMap.adjoint D B -
          a⁻¹ • LinearMap.adjoint (shiftedGaugeMap r ν D)
            (shiftedGaugeMap r ν D (LinearMap.adjoint D B))‖ ^ 2) →
    LinearMap.det (saddlePointOperator X (shiftedConstraint Q Dc ν)) ≠ 0 ∧
      LinearMap.det (saddlePointOperator (LinearMap.adjoint D ∘ₗ D) (shiftedGaugeMap r ν D)) ≠ 0 ∧
      constrainedGaussianNumber Q T =
        (2 * Real.pi) ^ (((Module.finrank ℝ A : ℝ) - (Module.finrank ℝ C : ℝ)) / 2) *
          a ^ (-(Module.finrank ℝ Gc : ℝ) / 2) *
          |LinearMap.det (saddlePointOperator X (shiftedConstraint Q Dc ν))| ^ (-(1 / 2) : ℝ) *
          |LinearMap.det (saddlePointOperator (LinearMap.adjoint D ∘ₗ D) (shiftedGaugeMap r ν D))|
end YangMills.Construction.GaussianConstraint
end
