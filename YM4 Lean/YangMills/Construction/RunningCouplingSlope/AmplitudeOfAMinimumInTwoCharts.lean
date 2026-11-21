import Mathlib
set_option autoImplicit false
noncomputable section
open scoped Topology Matrix
namespace YangMills.Construction.Slope
def hessianMatrix {X Ci : Type} [NormedAddCommGroup X] [NormedSpace ℝ X] [DecidableEq Ci]
    (c : X ≃ₗ[ℝ] (Ci → ℝ)) (S : X → ℝ) : Matrix Ci Ci ℝ :=
  Matrix.of fun i j => fderiv ℝ (fun ζ => fderiv ℝ S ζ (c.symm (Pi.single i 1))) 0 (c.symm (Pi.single j 1))
def HessianDetRatioInvariant : Prop :=
  ∀ (X : Type) [NormedAddCommGroup X] [NormedSpace ℝ X] [FiniteDimensional ℝ X]
    (Ci Oi Ti : Type) [Fintype Ci] [DecidableEq Ci] [Fintype Oi] [DecidableEq Oi] [Fintype Ti] [DecidableEq Ti]
    (c : X ≃ₗ[ℝ] (Ci → ℝ)) (e : Ci ⊕ Oi ≃ Ti) (S S' : X → ℝ) (Ψ : X × (Oi → ℝ) → Ti → ℝ) (ν : X → Ti → ℝ)
    (P P' : Matrix Ti Ci ℝ) (D D' : Matrix Ti Oi ℝ) (Θ : Matrix Ti Ti ℝ) (R : Matrix Oi Oi ℝ),
    ContDiffAt ℝ 2 Ψ 0 → Ψ 0 = 0 → (∀ x z, fderiv ℝ Ψ 0 (x, z) = P' *ᵥ c x + D' *ᵥ z) →
    ContDiffAt ℝ 2 ν 0 → ν 0 = 0 → (∀ x, fderiv ℝ ν 0 x = Θ *ᵥ (P *ᵥ c x)) →
    Θᵀ * Θ = 1 → Rᵀ * R = 1 → Θ * D = D' * R →
    ((Matrix.fromCols P D).submatrix id e.symm).det ≠ 0 →
    ((Matrix.fromCols P' D').submatrix id e.symm).det ≠ 0 →
    (∀ᶠ p in 𝓝 ((0 : X × (Oi → ℝ)), (0 : X)), Ψ p.1 = ν p.2 → S' p.1.1 = S p.2) →
    IsLocalMin S 0 → IsLocalMin S' 0 → (hessianMatrix c S').PosDef →
    (hessianMatrix c S).det * ((Matrix.fromCols P' D').submatrix id e.symm).det ^ 2 =
      (hessianMatrix c S').det * ((Matrix.fromCols P D).submatrix id e.symm).det ^ 2
end YangMills.Construction.Slope
end
