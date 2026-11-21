import YangMills.Construction.TransferOperators.FactsOfTheSquareRootOfTheBondKernel
import YangMills.Construction.TransferOperators.KernelBetweenTwoSquareRootsIsGaugeInvariantProof
import YangMills.Construction.TransferOperators.KernelBetweenTwoSquareRootsIsLinearAndReal
import Mathlib
set_option autoImplicit false
open MeasureTheory YangMills.Construction.SpinHarmonics YangMills.Construction.Matrices.ComplexMatrix2
noncomputable section
namespace YangMills.Construction.TransferOperators.SandwichKernelLinear
variable {t : ℝ} {E : Type} [Finite E]
theorem slice_ae_eq
    (hcont : Continuous fun q : (E → specialUnitary) × (E → specialUnitary) => sqrtLinkKernel t q.1 q.2)
    (v : E → specialUnitary) :
    ((sqrtLinkKernelSlice t v : HaarL2 E) : (E → specialUnitary) → ℂ)
      =ᵐ[haarPi E] fun x => sqrtLinkKernel t x v := by apply _root_.YangMills.Construction.TransferOperators.SandwichKernelGauge.slice_ae_eq <;> assumption
theorem sqrtKernelSandwich_linear (a b : ℂ) (S T : HaarL2 E →L[ℂ] HaarL2 E)
    (v v' : E → specialUnitary) :
    sqrtKernelSandwich t (a • S + b • T) v v' =
      a * sqrtKernelSandwich t S v v' + b * sqrtKernelSandwich t T v v' := by
  simp only [sqrtKernelSandwich, add_apply, smul_apply, inner_add_right, inner_smul_right]
theorem conj_eq_self_of_im_eq_zero {z : ℂ} (h : z.im = 0) : (starRingEnd ℂ) z = z :=
  Complex.conj_eq_iff_im.mpr h
theorem sqrtKernelSandwich_one
    (hre : ∀ v v' : E → specialUnitary, (sqrtLinkKernel t v v').im = 0)
    (hsymm : ∀ v v' : E → specialUnitary, sqrtLinkKernel t v v' = sqrtLinkKernel t v' v)
    (hcont : Continuous fun q : (E → specialUnitary) × (E → specialUnitary) => sqrtLinkKernel t q.1 q.2)
    (hsq : ∀ v v' : E → specialUnitary,
      ∫ x, sqrtLinkKernel t v x * sqrtLinkKernel t x v' ∂haarPi E = linkProductKernel t v v')
    (v v' : E → specialUnitary) : sqrtKernelSandwich t 1 v v' = linkProductKernel t v v' := by
  rw [← hsq v v']
  simp only [sqrtKernelSandwich, one_apply_eq_self]
  rw [L2.inner_def]
  refine integral_congr_ae ?_
  filter_upwards [slice_ae_eq hcont v, slice_ae_eq hcont v'] with x h₁ h₂
  rw [h₁, h₂, RCLike.inner_apply, conj_eq_self_of_im_eq_zero (hre x v), hsymm x v, mul_comm]
theorem sqrtKernelSandwich_im
    (hre : ∀ v v' : E → specialUnitary, (sqrtLinkKernel t v v').im = 0)
    (hcont : Continuous fun q : (E → specialUnitary) × (E → specialUnitary) => sqrtLinkKernel t q.1 q.2)
    (S : HaarL2 E →L[ℂ] HaarL2 E) (hS : IsRealPreserving S)
    (v v' : E → specialUnitary) : (sqrtKernelSandwich t S v v').im = 0 := by
  have slice_real : ∀ y : E → specialUnitary, ∀ᵐ x ∂haarPi E,
      (((sqrtLinkKernelSlice t y : HaarL2 E) : (E → specialUnitary) → ℂ) x).im = 0 := by
    intro y
    filter_upwards [slice_ae_eq hcont y] with x h
    rw [h]
    exact hre x y
  have hSy := hS _ (slice_real v')
  have hint : sqrtKernelSandwich t S v v' =
      ∫ x, (((((sqrtLinkKernelSlice t v : HaarL2 E) : (E → specialUnitary) → ℂ) x).re *
        (((S (sqrtLinkKernelSlice t v') : HaarL2 E) : (E → specialUnitary) → ℂ) x).re : ℝ) : ℂ)
        ∂haarPi E := by
    simp only [sqrtKernelSandwich]
    rw [L2.inner_def]
    refine integral_congr_ae ?_
    filter_upwards [slice_real v, hSy] with x h₁ h₂
    rw [RCLike.inner_apply, conj_eq_self_of_im_eq_zero h₁]
    apply Complex.ext <;> simp [h₁, h₂, mul_comm]
  rw [hint, integral_complex_ofReal]
  exact Complex.ofReal_im _
theorem sandwichKernelLinear_holds (hfacts : SqrtLinkFacts.SqrtLinkKernelFacts) :
    SandwichKernelLinearStatement := by
  intro t ht E _ _
  obtain ⟨⟨hre, hsymm, hcont⟩, -, -, -, -, -, -, ⟨-, hsq⟩, -, -⟩ := (hfacts t ht).1 E
  exact ⟨sqrtKernelSandwich_linear, sqrtKernelSandwich_one hre hsymm hcont hsq, fun S hS =>
    sqrtKernelSandwich_im hre hcont S hS⟩
end YangMills.Construction.TransferOperators.SandwichKernelLinear
end
