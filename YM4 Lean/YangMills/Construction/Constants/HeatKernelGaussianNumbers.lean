import Mathlib
set_option autoImplicit false
noncomputable section
namespace YangMills.Construction.Constants.HeatKernel
def halfLineSup (f : ℝ → ℝ) : ENNReal :=
  ⨆ (y : ℝ) (_ : 0 ≤ y), ENNReal.ofReal (f y)
def symmetryConstant : ℝ := 2 * Real.pi
def heatDecay : ℝ := 2 / Real.pi ^ 2
def factorialPower (n : ℕ) : ℝ := (n.factorial : ℝ) * symmetryConstant ^ n
def weightedFactorialPower (n : ℕ) : ENNReal :=
  ENNReal.ofReal (factorialPower n) *
    halfLineSup fun y => (1 + y) ^ n * Real.exp (-(heatDecay * y ^ 2))
def gaussianMoment (b : ℕ) : ENNReal :=
  halfLineSup fun y => y ^ b * Real.exp (-(1 / 2 * heatDecay * y ^ 2))
def binomialMoment (n b : ℕ) : ENNReal :=
  ∑ κ ∈ Finset.range (n + 1),
    (n.choose κ : ENNReal) * weightedFactorialPower (n - κ) * gaussianMoment (b - κ)
def shiftConstant : ℝ := Real.exp 1
def derivativeMoment (n b : ℕ) : ENNReal :=
  ENNReal.ofReal (Real.pi ^ ((3 : ℝ) / 2) * symmetryConstant) *
    (2 * binomialMoment n b + binomialMoment n (b + 1) +
      ENNReal.ofReal (2 ^ (n + 1) * Real.pi ^ 2) * binomialMoment n (b + 4))
def kernelDerivativeBound (n : ℕ) : ENNReal :=
  ENNReal.ofReal (2 ^ n / (2 * Real.pi)) *
    ({0, 1, 2} : Finset ℕ).sup fun b => max (derivativeMoment 0 b) (derivativeMoment n b)
def lowerDiagonalConstant : ℝ := 3 / (64 * Real.pi ^ 2)
def gaussianComparison (n : ℕ) : ENNReal :=
  max
    (max
      (ENNReal.ofReal (4 * shiftConstant) *
        ⨆ l : ℕ, ENNReal.ofReal ((2 * (l : ℝ) + 3) ^ n / (l.factorial : ℝ)))
      (ENNReal.ofReal (1 / (16 * Real.pi ^ 2)) *
        (halfLineSup fun y => (y ^ 4 + y ^ 3) * Real.exp (-(y / 8))) *
        halfLineSup fun y => (1 + y) ^ n * Real.exp (-(y ^ 2 / 8))))
    (4 * kernelDerivativeBound n ^ 4)
def fieldConstant : ENNReal :=
  (15 + 10368 + 1024 * 257 ^ 3) * gaussianComparison 6 + ENNReal.ofReal (8 * Real.pi ^ 2) +
    ENNReal.ofReal (1 / 2 * lowerDiagonalConstant)
end YangMills.Construction.Constants.HeatKernel
end
