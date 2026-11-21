import YangMills.Construction.FreeKernel.UnitLatticeHeatKernel
import Mathlib
set_option autoImplicit false
noncomputable section
namespace YangMills.Construction.FreeKernel
open YangMills.Construction.FreeKernel.UnitLattice
def IntegerHeatKernelEvolution : Prop :=
  (∀ n : ℤ, integerHeatKernel 0 n = if n = 0 then 1 else 0) ∧
  ∀ (T : ℝ) (n : ℤ), HasDerivAt (fun t => integerHeatKernel t n)
    (integerHeatKernel T (n + 1) + integerHeatKernel T (n - 1) - 2 * integerHeatKernel T n) T
end YangMills.Construction.FreeKernel
end
