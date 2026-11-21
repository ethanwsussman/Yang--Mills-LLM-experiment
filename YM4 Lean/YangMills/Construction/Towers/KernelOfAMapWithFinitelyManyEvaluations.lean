import YangMills.Construction.PeriodicOperators.SymmetricKernelOfAQuadraticForm
import Mathlib
set_option autoImplicit false
open Set
noncomputable section
namespace YangMills.Construction.Tower.FullSpace.FiniteSupportKernel
def KernelOfFiniteSupportMap : Prop :=
  ∀ (N N' : Type) (M : (N → ℂ) → N' → ℂ),
    (∀ f g, M (f + g) = M f + M g) → (∀ (c : ℂ) f, M (c • f) = c • M f) →
    (∀ j, ∃ A : Finset N, ∀ f g : N → ℂ, (∀ i ∈ A, f i = g i) → M f j = M g j) →
    PeriodicOperators.Represents (fun j i => M (PeriodicOperators.basisFunction i : N → ℂ) j) M ∧
      PeriodicOperators.kernelOfMap M =
        fun j i => M (PeriodicOperators.basisFunction i : N → ℂ) j
end YangMills.Construction.Tower.FullSpace.FiniteSupportKernel
end
