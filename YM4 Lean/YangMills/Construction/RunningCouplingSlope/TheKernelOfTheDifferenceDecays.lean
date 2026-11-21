import YangMills.Construction.RunningCouplingSlope.DifferenceOfTheTwoFunctionals
import Mathlib
set_option autoImplicit false
noncomputable section
namespace YangMills.Construction.RunningCouplingSlope
def DifferenceKernelExpDecay : Prop :=
  ∀ a : ℝ, 0 < a → ∀ L : ℕ, Conventions.IsAdmissibleBlockingFactor L →
    ∃ θ C : ℝ, 0 < θ ∧ 0 ≤ C ∧ ∀ k : ℕ, 1 ≤ k →
      ∃ κ : (Fin 4 → ℤ) → ℝ, IsDifferenceKernelLimit a L k κ ∧
        ∀ x, |κ x| ≤ C * Real.exp (-(θ * ∑ μ, |(x μ : ℝ)|))
end YangMills.Construction.RunningCouplingSlope
end
