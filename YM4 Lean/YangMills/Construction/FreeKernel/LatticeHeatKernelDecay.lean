import YangMills.Construction.FreeKernel.UnitLatticeHeatKernel
import Mathlib
set_option autoImplicit false
noncomputable section
namespace YangMills.Construction.FreeKernel
open YangMills.Construction.FreeKernel.UnitLattice
def LatticeHeatKernelDecayBound : Prop :=
  ∀ d : ℕ, ∃ c : ℝ, 0 ≤ c ∧ ∀ T : ℝ, 0 ≤ T → ∀ β : List (Fin d ⊕ Fin d), β.length ≤ 3 →
    ∀ n : Fin d → ℤ,
      |wordDiff β (latticeHeatKernel T) n| ≤
        c * (max T 1) ^ (-((d : ℝ) + (β.length : ℝ)) / 2) *
          Real.exp (-l1Length n / Real.sqrt (max T 1))
end YangMills.Construction.FreeKernel
end
