import YangMills.Construction.Conventions.PositiveConstant
import YangMills.Construction.Dirichlet.Parameters
import YangMills.Construction.FreeKernel.HolderFieldInteriorConstants
import Mathlib
set_option autoImplicit false
noncomputable section
namespace YangMills.Construction.FreeKernel.SecondDiff
open YangMills.Construction.FreeKernel YangMills.Construction.InfiniteLattice
lemma kernelConst_nonneg (hK : GreenKernelBounds) {d : ℕ} (hd : 3 ≤ d) :
    0 ≤ kernelConst d := by
  have hdecay := (hK d hd 1 one_pos).2.1 [] (by simp) (0 : GridSite d 1)
  have hlen : 0 ≤ gridLength (0 : GridSite d 1) := by
    unfold gridLength l1Length
    exact Finset.sum_nonneg fun _ _ => abs_nonneg _
  have hpos : 0 < gridLength (0 : GridSite d 1) + 1 := by linarith
  have hrpow := Real.rpow_pos_of_pos hpos (-((d : ℝ) - 2 + (([] : List (Fin d ⊕ Fin d)).length : ℝ)))
  exact nonneg_of_mul_nonneg_left ((abs_nonneg _).trans hdecay) hrpow
end YangMills.Construction.FreeKernel.SecondDiff
