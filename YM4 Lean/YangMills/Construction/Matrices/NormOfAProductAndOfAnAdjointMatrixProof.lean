import YangMills.Construction.Matrices.NormOfAProductAndOfAnAdjointMatrix
import Mathlib
set_option autoImplicit false
open scoped Matrix.Norms.L2Operator
noncomputable section
namespace YangMills.Construction.Matrices.RectangularMatrix.NormOfProductAndAdjoint
private theorem opNormValue_eq_l2_opNorm {n m : ℕ} [NeZero n] [NeZero m]
    (A : Matrix (Fin n) (Fin m) ℂ) :
    YangMills.Construction.Matrices.RectangularMatrix.opNormValue A = ‖A‖ :=
  (Matrix.l2_opNorm_def A).symm
theorem properties_holds :
    YangMills.Construction.Matrices.RectangularMatrix.NormOfProductAndAdjoint.Properties := by
  intro n m k _ _ _ A B c
  refine ⟨⟨fun v => ?_, ?_, ?_⟩, ?_⟩
  · rw [opNormValue_eq_l2_opNorm]
    exact Matrix.l2_opNorm_mulVec A (WithLp.toLp 2 v)
  · rw [opNormValue_eq_l2_opNorm, opNormValue_eq_l2_opNorm, opNormValue_eq_l2_opNorm]
    exact Matrix.l2_opNorm_mul A B
  · rw [opNormValue_eq_l2_opNorm, opNormValue_eq_l2_opNorm]
    exact norm_smul c A
  · unfold YangMills.Construction.Matrices.RectangularMatrix.NormOfProductAndAdjoint.AdjointNormEq
    rw [opNormValue_eq_l2_opNorm, opNormValue_eq_l2_opNorm]
    exact Matrix.l2_opNorm_conjTranspose A
end YangMills.Construction.Matrices.RectangularMatrix.NormOfProductAndAdjoint
