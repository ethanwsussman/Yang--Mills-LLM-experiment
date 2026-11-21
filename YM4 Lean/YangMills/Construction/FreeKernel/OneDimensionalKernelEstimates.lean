import YangMills.Construction.Constants.HeatKernelGaussianNumbers
import YangMills.Construction.FreeKernel.KernelsAndAbbreviationsInFourDimensions
import Mathlib
set_option autoImplicit false
noncomputable section
namespace YangMills.Construction.LatticeKernelBounds
open Complex LatticeKernel Constants.HeatKernel FourDimKernel
def besselSeriesTerm (t : ℝ) (j : ℤ) (l : ℕ) : ℝ :=
  t ^ (2 * l + j.natAbs) / ((l.factorial : ℝ) * ((l + j.natAbs).factorial : ℝ))
def HasBesselSeries : Prop :=
  ∀ (t : ℝ), 0 < t → ∀ j : ℤ, Summable (besselSeriesTerm t j) ∧
    discreteHeatKernel t j = ((Real.exp (-2 * t) * ∑' l, besselSeriesTerm t j l : ℝ) : ℂ)
def KernelPositive : Prop :=
  ∀ (t : ℝ), 0 < t → ∀ j : ℤ, (discreteHeatKernel t j).im = 0 ∧ 0 < (discreteHeatKernel t j).re
def KernelEven : Prop :=
  ∀ (t : ℝ), 0 < t → ∀ j : ℤ, discreteHeatKernel t (-j) = discreteHeatKernel t j
def KernelSumsToOne : Prop :=
  ∀ (t : ℝ), 0 < t → HasSum (discreteHeatKernel t) 1
def HasFourierExpansion : Prop :=
  ∀ (t : ℝ), 0 < t → ∀ θ : ℝ,
    Summable (fun j : ℤ => ‖discreteHeatKernel t j * Complex.exp (-(I * (j : ℂ) * (θ : ℂ)))‖) ∧
    HasSum (fun j : ℤ => discreteHeatKernel t j * Complex.exp (-(I * (j : ℂ) * (θ : ℂ))))
      ((Real.exp (-t * laplacianSymbol θ) : ℝ) : ℂ)
def ShortTimeBound : Prop :=
  ∀ (t : ℝ), 0 < t → t ≤ 1 → ∀ j : ℤ,
    (discreteHeatKernel t j).re ≤ shiftConstant * (t ^ j.natAbs / (j.natAbs.factorial : ℝ))
def LongTimeDecay (n : ℕ) (α : DiffKind) : Prop :=
  ∀ (t : ℝ), 1 ≤ t → ∀ j : ℤ,
    ‖diffOp α (discreteHeatKernel t) j‖ ≤
      (kernelDerivativeBound n).toReal * t ^ (-(((diffOrder α : ℝ) + 1) / 2)) *
        bracketOnePlus (|(j : ℝ)| / Real.sqrt t) ^ (-(n : ℝ))
def GaussianDerivDecay (n : ℕ) (α : DiffKind) : Prop :=
  ∀ (t : ℝ), 0 < t → ∀ ξ : ℝ,
    |gaussianHeatKernelDeriv (diffOrder α) t ξ| ≤
      (kernelDerivativeBound n).toReal * t ^ (-(((diffOrder α : ℝ) + 1) / 2)) *
        bracketOnePlus (|ξ| / Real.sqrt t) ^ (-(n : ℝ))
def GaussianComparison (n : ℕ) (α : DiffKind) : Prop :=
  ∀ (t : ℝ), 1 ≤ t → ∀ j : ℤ,
    ‖diffOp α (discreteHeatKernel t) j -
        ((gaussianHeatKernelDeriv (diffOrder α) t (j : ℝ) : ℝ) : ℂ)‖ ≤
      (kernelDerivativeBound n).toReal * t ^ (-(((diffOrder α : ℝ) + 2) / 2)) *
        bracketOnePlus (|(j : ℝ)| / Real.sqrt t) ^ (-(n : ℝ))
def OneDimensionalEstimates : Prop :=
  HasBesselSeries ∧ KernelPositive ∧ KernelEven ∧ KernelSumsToOne ∧ HasFourierExpansion ∧
    ShortTimeBound ∧
    ∀ n : ℕ, kernelDerivativeBound n ≠ ⊤ ∧ ∀ α : DiffKind,
      LongTimeDecay n α ∧ GaussianDerivDecay n α ∧ GaussianComparison n α
end YangMills.Construction.LatticeKernelBounds
end
