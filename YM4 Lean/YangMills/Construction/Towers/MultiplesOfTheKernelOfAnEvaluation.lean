import YangMills.Construction.Towers.TheScaledPicture
import Mathlib
set_option autoImplicit false
noncomputable section
namespace YangMills.Construction
namespace Tower
open PeriodicOperators (KernelUnique swapKernel)
namespace ScalarMultipleKernels
def CoeffsRealHomogeneous (r : PauliComponentsOfSymmetricKernel) : Prop :=
  ∀ (c : ℝ) (u : r.space.index → Matrices.ComplexMatrix2), r.coeffs (c • u) = (c : ℂ) • r.coeffs u
def Statement : Prop :=
  ∀ (r r' : PauliComponentsOfSymmetricKernel) (T : (r.space.index → Matrices.ComplexMatrix2) → r'.space.index → Matrices.ComplexMatrix2),
    CoeffsRealHomogeneous r' → PauliComponentsOfSymmetricKernel.HasLocalKernel r r' T →
    KernelUnique r.Index r'.Index → ∀ c s s' : ℝ,
      r.kernel r' (fun u => c • T u) = (c : ℂ) • r.kernel r' T ∧
      meshTranspose s s' (r.kernel r' fun u => c • T u) =
        ((c * (s' ^ 4 * (s ^ 4)⁻¹) : ℝ) : ℂ) • swapKernel (r.kernel r' T)
end ScalarMultipleKernels
end Tower
end YangMills.Construction
end
