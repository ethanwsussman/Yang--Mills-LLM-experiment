import YangMills.Construction.ColdStepAtMirrorFrames.ChangeAlongASegment
import YangMills.Construction.ColdStepAtMirrorFrames.SlopeAlongASegmentProof
import Mathlib
set_option autoImplicit false
noncomputable section
namespace YangMills.Construction.Calculus
namespace SegmentDiff
theorem weightedNorm_nonneg_of_nonneg {N : ℕ} {w : Fin N → ℝ} (hw : ∀ n, 0 ≤ w n) (x : Fin N → ℝ) :
    0 ≤ weightedNorm w x :=
  Finset.sum_nonneg fun n _ => mul_nonneg (abs_nonneg _) (hw n)
theorem weightedNorm_add_le_of_nonneg {N : ℕ} {w : Fin N → ℝ} (hw : ∀ n, 0 ≤ w n) (x y : Fin N → ℝ) :
    weightedNorm w (x + y) ≤ weightedNorm w x + weightedNorm w y := by apply _root_.YangMills.Construction.Calculus.weightedNorm_add_le <;> assumption
theorem weightedNorm_const_smul {N : ℕ} (w : Fin N → ℝ) (c : ℝ) (x : Fin N → ℝ) :
    weightedNorm w (c • x) = |c| * weightedNorm w x := by apply _root_.YangMills.Construction.Calculus.weightedNorm_smul <;> assumption
theorem abs_multilinear_le_mul_prod_weightedNorm {N j : ℕ}
    (T : ContinuousMultilinearMap ℝ (fun _ : Fin j => Fin N → ℝ) ℝ) (K : ℝ)
    (w : Fin N → ℝ) (hw : ∀ n, 0 ≤ w n) (hK : 0 ≤ K)
    (hT : ∀ r : Fin j → Fin N, |T (fun i => Pi.single (r i) 1)| ≤ K * ∏ i, w (r i))
    (ξ : Fin j → Fin N → ℝ) : |T ξ| ≤ K * ∏ i, weightedNorm w (ξ i) := by apply _root_.YangMills.Construction.Calculus.abs_multilinear_le_prod_weightedNorm <;> assumption
end SegmentDiff

end YangMills.Construction.Calculus
end
