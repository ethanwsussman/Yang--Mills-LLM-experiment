import Mathlib
set_option autoImplicit false
open MeasureTheory Set
noncomputable section
namespace YangMills.Construction
namespace Schatten
section IntegralOperators
variable {X : Type*} [TopologicalSpace X]
variable [MeasurableSpace X] (μ : Measure X)
def kernelApply (K : X × X → ℂ) (f : Lp ℂ 2 μ) (x : X) : ℂ :=
  ∫ y, K (x, y) * f y ∂μ
def HasKernel (K : X × X → ℂ) (T : Lp ℂ 2 μ →L[ℂ] Lp ℂ 2 μ) : Prop :=
  ∀ f, T f =ᵐ[μ] kernelApply μ K f
def kernelOp (K : X × X → ℂ) : Lp ℂ 2 μ →L[ℂ] Lp ℂ 2 μ :=
  Classical.epsilon (HasKernel μ K)
end IntegralOperators
end Schatten
end YangMills.Construction
