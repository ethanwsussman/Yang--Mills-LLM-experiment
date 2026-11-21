import YangMills.Construction.RunningCouplingSlope.DifferenceOfTheTwoFunctionals
import Mathlib
set_option autoImplicit false
open Filter
open scoped Topology
noncomputable section
namespace YangMills.Construction.RunningCouplingSlope
def DifferenceKernelLimitExists.Claim : Prop :=
  ∀ a : ℝ, 0 < a → ∀ L : ℕ, Conventions.IsAdmissibleBlockingFactor L → ∀ k : ℕ, 1 ≤ k →
    ∃ κ : (Fin 4 → ℤ) → ℝ, IsDifferenceKernelLimit a L k κ
end YangMills.Construction.RunningCouplingSlope
end
