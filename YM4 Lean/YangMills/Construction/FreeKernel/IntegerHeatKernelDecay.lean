import YangMills.Construction.FreeKernel.UnitLatticeHeatKernel
import Mathlib
set_option autoImplicit false
noncomputable section
namespace YangMills.Construction.FreeKernel
open YangMills.Construction.FreeKernel.UnitLattice
def IntegerHeatKernelDecayBound : Prop :=
  ∃ c : ℝ, 0 ≤ c ∧ ∀ T : ℝ, 0 ≤ T → ∀ a a' : ℕ, a + a' ≤ 3 → ∀ n : ℤ,
    |forwardDiff^[a] (backwardDiff^[a'] (integerHeatKernel T)) n| ≤
      c * (max T 1) ^ (-((1 : ℝ) + a + a') / 2) * Real.exp (-|(n : ℝ)| / Real.sqrt (max T 1))
end YangMills.Construction.FreeKernel
end
