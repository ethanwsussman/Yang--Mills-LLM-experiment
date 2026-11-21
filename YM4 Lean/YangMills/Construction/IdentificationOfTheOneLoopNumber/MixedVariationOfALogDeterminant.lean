import Mathlib
set_option autoImplicit false
open Filter Topology
noncomputable section
namespace YangMills.Construction.OneLoopCoefficient
def hasDerivAt_mixed_logDet_statement : Prop :=
  ∀ (ι : Type) [Fintype ι] [DecidableEq ι] (K : ℝ → ℝ → Matrix ι ι ℂ) (K₁ K₁' K₂ : Matrix ι ι ℂ),
    (∀ᶠ u in 𝓝 (0 : ℝ), ∀ i j, DifferentiableAt ℝ (fun t => K u t i j) 0) →
    (∀ i j, HasDerivAt (fun u => K u 0 i j) (K₁ i j) 0) →
    (∀ i j, HasDerivAt (fun t => K 0 t i j) (K₁' i j) 0) →
    (∀ i j, HasDerivAt (fun u => deriv (fun t => K u t i j) 0) (K₂ i j) 0) →
    (K 0 0).det ∈ Complex.slitPlane →
    (∀ᶠ u in 𝓝 (0 : ℝ), DifferentiableAt ℝ (fun t => Complex.log (K u t).det) 0) ∧
      HasDerivAt (fun u => deriv (fun t => Complex.log (K u t).det) 0)
        (((K 0 0)⁻¹ * K₂).trace - ((K 0 0)⁻¹ * K₁ * ((K 0 0)⁻¹ * K₁')).trace) 0
end YangMills.Construction.OneLoopCoefficient
