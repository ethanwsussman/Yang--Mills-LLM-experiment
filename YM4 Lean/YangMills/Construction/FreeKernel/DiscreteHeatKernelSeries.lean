import YangMills.Construction.Constants.HeatKernelGaussianNumbers
import YangMills.Construction.FreeKernel.OneDimensionalLatticeKernels
import Mathlib
set_option autoImplicit false
noncomputable section
namespace YangMills.Construction.FreeKernel
open Complex
open YangMills.Construction.LatticeKernel YangMills.Construction.Constants.HeatKernel
def DiscreteHeatKernelSeries : Prop :=
  (∀ (t : ℝ), 0 < t → ∀ j : ℤ,
    Summable (fun l : ℕ => t ^ (2 * l + j.natAbs) /
      ((l.factorial : ℝ) * ((l + j.natAbs).factorial : ℝ))) ∧
    discreteHeatKernel t j = ((Real.exp (-2 * t) * ∑' l : ℕ, t ^ (2 * l + j.natAbs) /
      ((l.factorial : ℝ) * ((l + j.natAbs).factorial : ℝ)) : ℝ) : ℂ)) ∧
  (∀ (t : ℝ), 0 < t → ∀ j : ℤ, (discreteHeatKernel t j).im = 0 ∧ 0 < (discreteHeatKernel t j).re) ∧
  (∀ (t : ℝ), 0 < t → ∀ j : ℤ, discreteHeatKernel t (-j) = discreteHeatKernel t j) ∧
  (∀ (t : ℝ), 0 < t → HasSum (discreteHeatKernel t) 1) ∧
  (∀ (t : ℝ), 0 < t → ∀ x : ℝ,
    Summable (fun j : ℤ => ‖discreteHeatKernel t j * Complex.exp (-(I * (j : ℂ) * (x : ℂ)))‖) ∧
    HasSum (fun j : ℤ => discreteHeatKernel t j * Complex.exp (-(I * (j : ℂ) * (x : ℂ))))
      ((Real.exp (-t * laplacianSymbol x) : ℝ) : ℂ)) ∧
  (∀ (t : ℝ), 0 < t → t ≤ 1 → ∀ j : ℤ,
    (discreteHeatKernel t j).re ≤ shiftConstant * (t ^ j.natAbs / (j.natAbs.factorial : ℝ)))
end YangMills.Construction.FreeKernel
end
