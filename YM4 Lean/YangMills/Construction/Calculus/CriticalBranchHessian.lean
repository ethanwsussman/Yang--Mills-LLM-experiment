import Mathlib
set_option autoImplicit false
open Filter
open scoped Topology
noncomputable section
namespace YangMills.Construction.Calculus
def CriticalBranchHessian : Prop :=
  ∀ (V U : Type) [NormedAddCommGroup V] [NormedSpace ℝ V] [NormedAddCommGroup U] [NormedSpace ℝ U]
    (H : V × U → ℝ) (β : V → U) (v₀ : V),
    ContDiffAt ℝ 2 H (v₀, β v₀) → ContDiffAt ℝ 2 β v₀ →
    (∀ᶠ v in 𝓝 v₀, ∀ k : U, fderiv ℝ (fun u => H (v, u)) (β v) k = 0) →
    (fderiv ℝ (fun v => H (v, β v)) v₀ = 0 → fderiv ℝ H (v₀, β v₀) = 0) ∧
    (∀ k k' : U, fderiv ℝ (fderiv ℝ fun u => H (v₀, u)) (β v₀) k k' =
      fderiv ℝ (fderiv ℝ H) (v₀, β v₀) (0, k) (0, k')) ∧
    ∀ (h : V) (k : U), fderiv ℝ (fderiv ℝ H) (v₀, β v₀) (h, k) (h, k) =
      fderiv ℝ (fderiv ℝ fun v => H (v, β v)) v₀ h h +
      fderiv ℝ (fderiv ℝ H) (v₀, β v₀) (0, k - fderiv ℝ β v₀ h) (0, k - fderiv ℝ β v₀ h)
end YangMills.Construction.Calculus
end
