import YangMills.Construction.ResponseInTheExpansion.KernelOfTheCurvature
import Mathlib
set_option autoImplicit false
noncomputable section
namespace YangMills.Construction.LinearResponse
open TorusFields
def TorusDisplacementNearSites : Prop :=
  ∀ (N : ℕ) [NeZero N] (z z' : TorusSite N),
    (∀ a b : TorusSite N, (∀ μ, |torusDisplacement z z' μ| + (supDist a z : ℝ) + (supDist b z' : ℝ) < (N : ℝ) / 2) →
      ∀ μ, |torusDisplacement a b μ - torusDisplacement z z' μ| ≤ (supDist a z : ℝ) + (supDist b z' : ℝ)) ∧
    (∀ μ, |torusDisplacement z z' μ| < (N : ℝ) / 2 → torusDisplacement z' z μ = -torusDisplacement z z' μ) ∧
    ∀ u u' : Fin 4 → ℝ, (∀ μ, ((z μ).val : ℝ) ≤ u μ ∧ u μ < (z μ).val + 1) →
      (∀ μ, ((z' μ).val : ℝ) ≤ u' μ ∧ u' μ < (z' μ).val + 1) →
      (∀ μ, |torusDisplacement z z' μ| + 1 < (N : ℝ) / 2) →
      ∀ μ, |circleSub N (u' μ) (u μ) - torusDisplacement z z' μ| ≤ 1
end YangMills.Construction.LinearResponse
end
