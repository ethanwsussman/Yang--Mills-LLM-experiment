import YangMills.Construction.Constants.HeatKernelGaussianNumbers
import Mathlib
set_option autoImplicit false
noncomputable section
namespace YangMills.Construction.Constants.HeatKernel
def finite_and_pos : Prop :=
  0 < symmetryConstant ∧ 0 < heatDecay ∧ 0 < shiftConstant ∧ 0 < lowerDiagonalConstant ∧
  (∀ n : ℕ, 0 < factorialPower n) ∧
  (∀ n : ℕ, weightedFactorialPower n ≠ ⊤ ∧ 0 < weightedFactorialPower n) ∧
  (∀ b : ℕ, gaussianMoment b ≠ ⊤ ∧ 0 < gaussianMoment b) ∧
  (∀ n b : ℕ, binomialMoment n b ≠ ⊤ ∧ 0 < binomialMoment n b) ∧
  (∀ n b : ℕ, derivativeMoment n b ≠ ⊤ ∧ 0 < derivativeMoment n b) ∧
  (∀ n : ℕ, kernelDerivativeBound n ≠ ⊤ ∧ 0 < kernelDerivativeBound n) ∧
  (∀ n : ℕ, gaussianComparison n ≠ ⊤ ∧ 0 < gaussianComparison n) ∧
  (fieldConstant ≠ ⊤ ∧ 0 < fieldConstant) ∧
  2 ≤ symmetryConstant ∧ 2 * heatDecay ≤ 1 ∧ 1 / 2 * heatDecay = Real.pi ^ (-2 : ℤ) ∧
  gaussianMoment 0 = 1
end YangMills.Construction.Constants.HeatKernel
end
