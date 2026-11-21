import YangMills.Construction.ResponseInTheExpansion.SizeOfAKernel
import YangMills.Construction.ResponseInTheExpansion.TheStepDensityProof
import Mathlib
set_option autoImplicit false
noncomputable section
open scoped Quaternion
open MeasureTheory
namespace YangMills.Construction.ResponseInTheExpansion
open YangMills.Construction.TorusLumps YangMills.Construction.TorusFields
open YangMills.Construction.StepCosts YangMills.Construction.WeightedResponses
open YangMills.Construction.BlockAverages YangMills.Construction.LumpContours
namespace KernelSize
theorem exp_neg_abs_le_partitionFn (s : ℝ) : Real.exp (-|s|) ≤ partitionFn s := by apply _root_.YangMills.Construction.WeightedResponses.exp_neg_abs_le_partitionFn <;> assumption
variable {n : ℕ} [NeZero n]
theorem bondKernel_le_exp (ℓ : StepParameters) (x : ℝ) (w : (stepBlockFrame ℓ.side n).GaugeField 0)
    (v : (stepBlockFrame ℓ.side n).GaugeField 1)
    (b : BaseChoice ℓ.side n) (c : (stepBlockFrame ℓ.side n).Cell × Fin 4) :
    bondKernel ℓ x w v b c ≤ Real.exp (2 * |ℓ.coupling * x|) := by apply _root_.YangMills.Construction.WeightedResponses.bondKernel_le_exp <;> assumption
theorem bondKernelBounds_holds : BondKernelBounds := by
  intro ℓ x n _ W V b c
  have hc := bondKernel_le_exp ℓ x (readAtLevel (stepBlockFrame ℓ.side n) 0 W)
    (readAtLevel (stepBlockFrame ℓ.side n) 1 V) b
    (torusSiteInFrame (stepBlockFrame ℓ.side n) 1 c.1, c.2)
  refine ⟨?_, hc⟩
  unfold bondKernelAt bondKernel
  simp only
  refine div_pos (Real.exp_pos _) (lt_of_lt_of_le (Real.exp_pos _) (exp_neg_abs_le_partitionFn _))
end KernelSize
end YangMills.Construction.ResponseInTheExpansion
end
