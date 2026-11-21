import YangMills.Construction.Continuum.SchwartzTestsAndMollifiers
import YangMills.Construction.EuclideanFunctionals.MultiIndicesConvolutionsAndSeriesOfOperators
import Mathlib
set_option autoImplicit false
open Set
open scoped ContDiff
noncomputable section
namespace YangMills.Construction.CubeKernels
def IsPlateauBump (χ : ℝ → ℝ) : Prop :=
  ContDiff ℝ ∞ χ ∧ HasCompactSupport χ ∧ (∀ t, 0 ≤ χ t ∧ χ t ≤ 1) ∧
    (∀ t ∈ Icc (-(1 / 2) : ℝ) (1 / 2), χ t = 1) ∧ ∀ t, t ∉ Icc (-1 : ℝ) 1 → χ t = 0
def plateauBump : ℝ → ℝ := Classical.epsilon IsPlateauBump
def quadBump (t : ℝ) : ℝ := 1 / 2 * max t 0 ^ 2 * plateauBump t
def thirdDerivBump (t : ℝ) : ℝ :=
  if 0 < t then
    -(3 * deriv plateauBump t + 3 * t * deriv (deriv plateauBump) t +
      1 / 2 * t ^ 2 * deriv (deriv (deriv plateauBump)) t)
  else 0
def quadBumpScaled (υ t : ℝ) : ℝ := υ ^ 2 * quadBump (t / υ)
def thirdDerivBumpScaled (υ t : ℝ) : ℝ := υ⁻¹ * thirdDerivBump (t / υ)
def cubeKernel (Γ : Finset (Fin 4)) (υ : ℝ) (x : Fin 4 → ℝ) : ℝ :=
  (∏ μ ∈ Γ, quadBumpScaled υ (x μ)) * ∏ μ ∈ Γᶜ, thirdDerivBumpScaled υ (x μ)
def cubedPartial (Γ : Finset (Fin 4)) (h : (Fin 4 → ℝ) → ℂ) : (Fin 4 → ℝ) → ℂ :=
  YangMills.Construction.EuclideanFunctionals.iteratedPartial (fun μ => if μ ∈ Γ then 3 else 0) h
def cubeKernelConst : ℝ :=
  5 * max 1 (max (YangMills.Construction.TestFunctions.uniformNorm quadBump)
    (max (YangMills.Construction.TestFunctions.uniformNorm (deriv quadBump))
    (max (YangMills.Construction.TestFunctions.uniformNorm thirdDerivBump)
      (YangMills.Construction.TestFunctions.uniformNorm (deriv thirdDerivBump))))) ^ 4
def SupportsInCube : Prop :=
  ContDiff ℝ 1 quadBump ∧ HasCompactSupport quadBump ∧ tsupport quadBump ⊆ Icc 0 1 ∧
    ContDiff ℝ ∞ thirdDerivBump ∧ HasCompactSupport thirdDerivBump ∧
    tsupport thirdDerivBump ⊆ Icc 0 1 ∧
    ∀ (Γ : Finset (Fin 4)) (υ : ℝ), 0 < υ →
      cubeKernel Γ υ ∈ YangMills.Construction.FourSpace.C1c ∧
        tsupport (cubeKernel Γ υ) ⊆ {x | ∀ μ, x μ ∈ Icc 0 υ}
def ReproducingIdentity : Prop :=
  ∀ h : (Fin 4 → ℝ) → ℂ, ContDiff ℝ ∞ h → HasCompactSupport h → ∀ υ : ℝ, 0 < υ →
    h = ∑ Γ : Finset (Fin 4),
      YangMills.Construction.EuclideanFunctionals.conv (fun x => (cubeKernel Γ υ x : ℂ))
        (cubedPartial Γ h)
def KernelNormBound : Prop :=
  ∀ (Γ : Finset (Fin 4)) (υ : ℝ), 0 < υ → υ ≤ 1 →
    YangMills.Construction.WightmanReconstruction.supC1Norm (fun x => (cubeKernel Γ υ x : ℂ)) ≤
      cubeKernelConst * υ ^ (3 * (Γ.card : ℤ) - 5)
def KernelFacts : Prop :=
  IsPlateauBump plateauBump ∧ SupportsInCube ∧ ReproducingIdentity ∧ KernelNormBound
end YangMills.Construction.CubeKernels
