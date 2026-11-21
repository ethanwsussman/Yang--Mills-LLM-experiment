import YangMills.Construction.TransferOperators.FactsOfTheSquareRootOfTheBondKernel
import YangMills.Construction.TransferOperators.KernelBetweenTwoSquareRootsIsGaugeInvariantProof
import YangMills.Construction.TransferOperators.OperatorBetweenTwoSquareRootsIsOfTraceClass
import Mathlib
set_option autoImplicit false
open MeasureTheory YangMills.Construction.SpinHarmonics YangMills.Construction.Matrices.ComplexMatrix2
noncomputable section
namespace YangMills.Construction.TransferOperators.SandwichTraceClass
variable {t : ℝ} {E : Type} [Finite E]
theorem slice_ae_eq
    (hcont : Continuous fun q : (E → specialUnitary) × (E → specialUnitary) => sqrtLinkKernel t q.1 q.2)
    (v : E → specialUnitary) :
    ((sqrtLinkKernelSlice t v : HaarL2 E) : (E → specialUnitary) → ℂ)
      =ᵐ[haarPi E] fun x => sqrtLinkKernel t x v := by apply _root_.YangMills.Construction.TransferOperators.SandwichKernelGauge.slice_ae_eq <;> assumption
theorem kernelApply_eq_inner
    (hre : ∀ v v' : E → specialUnitary, (sqrtLinkKernel t v v').im = 0)
    (hsymm : ∀ v v' : E → specialUnitary, sqrtLinkKernel t v v' = sqrtLinkKernel t v' v)
    (hcont : Continuous fun q : (E → specialUnitary) × (E → specialUnitary) => sqrtLinkKernel t q.1 q.2)
    (F : HaarL2 E) (v : E → specialUnitary) :
    Schatten.kernelApply (haarPi E) (fun q => sqrtLinkKernel t q.1 q.2) F v =
      inner ℂ (sqrtLinkKernelSlice t v) F := by
  rw [L2.inner_def]
  simp only [Schatten.kernelApply]
  refine integral_congr_ae ?_
  filter_upwards [slice_ae_eq hcont v] with x h
  rw [h, RCLike.inner_apply, Complex.conj_eq_iff_im.mpr (hre x v), hsymm x v, mul_comm]
theorem sqrtLinkOperator_apply_ae
    (hK : Schatten.HasKernel (haarPi E)
      (fun q => sqrtLinkKernel t q.1 q.2) (sqrtLinkOperator t E))
    (hre : ∀ v v' : E → specialUnitary, (sqrtLinkKernel t v v').im = 0)
    (hsymm : ∀ v v' : E → specialUnitary, sqrtLinkKernel t v v' = sqrtLinkKernel t v' v)
    (hcont : Continuous fun q : (E → specialUnitary) × (E → specialUnitary) => sqrtLinkKernel t q.1 q.2)
    (F : HaarL2 E) :
    ((sqrtLinkOperator t E F : HaarL2 E) : (E → specialUnitary) → ℂ)
      =ᵐ[haarPi E] fun v => inner ℂ (sqrtLinkKernelSlice t v) F := by
  filter_upwards [hK F] with v h
  rw [h, kernelApply_eq_inner hre hsymm hcont]
theorem sandwich_hasKernel
    (hK : Schatten.HasKernel (haarPi E)
      (fun q => sqrtLinkKernel t q.1 q.2) (sqrtLinkOperator t E))
    (hself : IsSymmetricOp (sqrtLinkOperator t E))
    (hre : ∀ v v' : E → specialUnitary, (sqrtLinkKernel t v v').im = 0)
    (hsymm : ∀ v v' : E → specialUnitary, sqrtLinkKernel t v v' = sqrtLinkKernel t v' v)
    (hcont : Continuous fun q : (E → specialUnitary) × (E → specialUnitary) => sqrtLinkKernel t q.1 q.2)
    (S : HaarL2 E →L[ℂ] HaarL2 E) :
    Schatten.HasKernel (haarPi E)
      (fun q => sqrtKernelSandwich t S q.1 q.2)
      (sqrtLinkOperator t E * S * sqrtLinkOperator t E) := by
  intro f
  have hcomp : (sqrtLinkOperator t E * S * sqrtLinkOperator t E) f =
      sqrtLinkOperator t E (S (sqrtLinkOperator t E f)) := rfl
  rw [hcomp]
  filter_upwards [sqrtLinkOperator_apply_ae hK hre hsymm hcont (S (sqrtLinkOperator t E f))] with v hv
  rw [hv]
  have hmove : inner ℂ (sqrtLinkKernelSlice t v) (S (sqrtLinkOperator t E f)) =
      inner ℂ (sqrtLinkOperator t E
        (ContinuousLinearMap.adjoint S (sqrtLinkKernelSlice t v))) f := by
    rw [← hself, ContinuousLinearMap.adjoint_inner_left]
  rw [hmove, L2.inner_def]
  simp only [Schatten.kernelApply]
  refine integral_congr_ae ?_
  filter_upwards [sqrtLinkOperator_apply_ae hK hre hsymm hcont
    (ContinuousLinearMap.adjoint S (sqrtLinkKernelSlice t v))] with v' h
  rw [h, ContinuousLinearMap.adjoint_inner_right, RCLike.inner_apply, inner_conj_symm, mul_comm]
  rfl
theorem isHilbertSchmidtPW_comp_left (S A : HaarL2 E →L[ℂ] HaarL2 E)
    (hA : IsHilbertSchmidtPW A) : IsHilbertSchmidtPW (S * A) := by
  refine Summable.of_nonneg_of_le (fun _ => by positivity) (fun i => ?_) (hA.mul_left (‖S‖ ^ 2))
  rw [← mul_pow]
  exact pow_le_pow_left₀ (norm_nonneg _) (S.le_opNorm _) 2
theorem sandwichTraceClass_holds (hfacts : SqrtLinkFacts.SqrtLinkKernelFacts)
    (hgibbs : GibbsHaarKernels.Statement) : SandwichTraceClassStatement := by
  intro t ht E _ _ S
  obtain ⟨⟨hre, hsymm, hcont⟩, -, -, -, -, ⟨-, hself, -⟩, -, -, ⟨hhs, -⟩, -⟩ := (hfacts t ht).1 E
  have hK := ((hgibbs.2.2.2 E).1 _ hcont).2.1
  exact ⟨⟨_, _, hhs, isHilbertSchmidtPW_comp_left S _ hhs, mul_assoc _ _ _⟩,
    sandwich_hasKernel hK hself hre hsymm hcont S⟩
end YangMills.Construction.TransferOperators.SandwichTraceClass
end
