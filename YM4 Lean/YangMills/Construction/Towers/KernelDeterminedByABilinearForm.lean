import YangMills.Construction.PeriodicOperators.ProductsOfKernelsWithFiniteRows
import Mathlib
set_option autoImplicit false
noncomputable section
namespace YangMills.Construction
namespace Tower
open PeriodicOperators (KernelMatrix applyKernel unitKernel RowFinite HasFiniteSupport)
namespace PolarisedKernel
variable {N : Type}
structure IsSymmBilinearOnFinite (β : (N → ℂ) → (N → ℂ) → ℂ) : Prop where
  add_smul_left : ∀ (z : ℂ) (f g h : N → ℂ), HasFiniteSupport f → HasFiniteSupport g →
    HasFiniteSupport h → β (z • f + g) h = z * β f h + β g h
  symm : ∀ f g : N → ℂ, HasFiniteSupport f → HasFiniteSupport g → β f g = β g f
def ValueAtUnits : Prop :=
  ∀ (N : Type) (T : KernelMatrix N N) (w : ℝ) (β : (N → ℂ) → (N → ℂ) → ℂ), RowFinite T →
    (∀ s t, T s t = T t s) → IsSymmBilinearOnFinite β →
    (∀ c : N → ℂ, HasFiniteSupport c →
      β c c = PeriodicOperators.wPairing (fun _ => w) c (applyKernel T c)) →
    ∀ s t : N, β (fun r => unitKernel N r s) (fun r => unitKernel N r t) = (w : ℂ) * T s t
end PolarisedKernel
end Tower
end YangMills.Construction
end
