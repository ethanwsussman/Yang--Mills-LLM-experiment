import YangMills.Construction.LawInAState.FormsOnAnEvent
import Mathlib
set_option autoImplicit false
noncomputable section
namespace YangMills.Construction.QuadraticConcentration
structure BoxSizes (Cm x lam A φ ε ρ η err D τ : ℝ) : Prop where
  lam_pos : 0 < lam
  lam_le : lam ≤ x ^ (-1 + 1 / 10000 : ℝ)
  one_le_A : 1 ≤ A
  A_le : A ≤ x ^ (1 / 25 + 1 / 10000 : ℝ)
  φ_nonneg : 0 ≤ φ
  φ_le : φ ≤ x ^ (-(1 / 2) - 2 / 81 + 1 / 10000 : ℝ)
  ε_nonneg : 0 ≤ ε
  ε_le : ε ≤ x ^ (-20 : ℝ)
  ρ_nonneg : 0 ≤ ρ
  ρ_le : ρ ≤ x ^ (2 * (1 / 50 - 2 / 27 + 1 / 10000) : ℝ)
  η_pos : 0 < η
  η_le : η ≤ x ^ (-(1 / 7) : ℝ)
  err_nonneg : 0 ≤ err
  err_le : err ≤ x ^ (-(11 / 10) : ℝ)
  D_nonneg : 0 ≤ D
  D_le : D ≤ x ^ Cm
  τ_nonneg : 0 ≤ τ
  τ_le : τ ≤ x ^ (-(32 * (2 * Cm + 4)) : ℝ)
def boxExponentsStatement : Prop :=
  ∀ C₀ Cm : ℝ, 1 ≤ C₀ → 0 ≤ Cm → ∃ C x₀ : ℝ, 1 ≤ x₀ ∧ ∀ x lam A φ ε ρ η err D τ : ℝ, x₀ ≤ x →
    BoxSizes Cm x lam A φ ε ρ η err D τ →
      productBoundOnEvent C₀ lam A φ ε ρ η err D τ ≤ C * x ^ (-(2 + 1 / 130) : ℝ) ∧
      meanBoundOnEvent C₀ lam A φ ε ρ η err D τ ≤ C * x ^ (-(1 + 1 / 130) : ℝ)
end YangMills.Construction.QuadraticConcentration
end
