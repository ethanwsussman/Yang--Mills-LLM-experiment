import YangMills.Construction.LawByMomentsOfTheFlow.FactsOfAReflection
import Mathlib
set_option autoImplicit false
noncomputable section
namespace YangMills.Construction.CyclicFormula
private theorem sum_orderedDirectionPair (g : Fin 4 × Fin 4 → ℝ) :
    ∑ p : OrderedDirectionPair, g p.1 = g (0, 1) + g (0, 2) + g (0, 3) + g (1, 2) + g (1, 3) + g (2, 3) := by
  have h : ∑ p : OrderedDirectionPair, g p.1 = ∑ x ∈ Finset.univ.filter (fun x : Fin 4 × Fin 4 => x.1 < x.2), g x :=
    (Finset.sum_subtype _ (by simp) g).symm
  rw [h, Finset.sum_filter, Fintype.sum_prod_type]
  simp [Fin.sum_univ_four]
  ring
private theorem exteriorSquareTrace_eq (A : Matrix (Fin 4) (Fin 4) ℝ) :
    exteriorSquareTrace A = ((Matrix.trace A) ^ 2 - Matrix.trace (A * A)) / 2 := by
  have h : exteriorSquareTrace A = ∑ p : OrderedDirectionPair, (fun e : Fin 4 × Fin 4 => A e.1 e.1 * A e.2 e.2 - A e.1 e.2 * A e.2 e.1) p.1 := by
    simp only [exteriorSquareTrace, Matrix.trace, Matrix.diag, exteriorSquareMap]
  rw [h]
  refine (sum_orderedDirectionPair (fun e : Fin 4 × Fin 4 => A e.1 e.1 * A e.2 e.2 - A e.1 e.2 * A e.2 e.1)).trans ?_
  simp only [Matrix.trace, Matrix.diag, Matrix.mul_apply, Fin.sum_univ_four]
  ring
private theorem sum_mul_self_eq_norm_sq (x : TestFunctions.EuclideanFourSpace) : ∑ a, x a * x a = ‖x‖ ^ 2 := by
  rw [EuclideanSpace.norm_eq, Real.sq_sqrt (Finset.sum_nonneg fun _ _ => by positivity)]
  exact Finset.sum_congr rfl fun a _ => by rw [Real.norm_eq_abs, sq_abs, sq]
private theorem vecMulVec_mul_self (x : TestFunctions.EuclideanFourSpace) :
    Matrix.vecMulVec (fun a => x a) (fun a => x a) * Matrix.vecMulVec (fun a => x a) (fun a => x a) =
      (‖x‖ ^ 2) • Matrix.vecMulVec (fun a => x a) (fun a => x a) := by
  ext a b
  simp only [Matrix.mul_apply, Matrix.vecMulVec_apply, Matrix.smul_apply, smul_eq_mul, ← sum_mul_self_eq_norm_sq]
  rw [Finset.sum_mul]
  exact Finset.sum_congr rfl fun e _ => by ring
private theorem inversionMatrix_zero : inversionMatrix 0 = 1 := by
  ext a b
  simp [inversionMatrix]
private theorem inversionMatrix_mul_self (x : TestFunctions.EuclideanFourSpace) :
    inversionMatrix x * inversionMatrix x = 1 := by
  by_cases hx : x = 0
  · subst hx
    rw [inversionMatrix_zero, one_mul]
  have h2 : (2 / ‖x‖ ^ 2) * ((2 / ‖x‖ ^ 2) * ‖x‖ ^ 2) = 2 / ‖x‖ ^ 2 + 2 / ‖x‖ ^ 2 := by
    field_simp
    ring
  simp only [inversionMatrix, Matrix.sub_mul, Matrix.mul_sub, Matrix.one_mul, Matrix.mul_one,
    Matrix.smul_mul, Matrix.mul_smul, vecMulVec_mul_self, smul_smul, smul_sub, h2, add_smul]
  abel
private theorem inversionMatrix_det (x : TestFunctions.EuclideanFourSpace) (hx : x ≠ 0) :
    (inversionMatrix x).det = -1 := by
  have h : inversionMatrix x = 1 + Matrix.replicateCol Unit (fun a => -(2 / ‖x‖ ^ 2) * x a) *
      Matrix.replicateRow Unit (fun a => x a) := by
    ext a b
    simp [inversionMatrix, Matrix.mul_apply, Matrix.vecMulVec_apply, sub_eq_add_neg]
    ring
  rw [h, Matrix.det_one_add_replicateCol_mul_replicateRow]
  have : (fun a => x a) ⬝ᵥ (fun a => -(2 / ‖x‖ ^ 2) * x a) = -(2 / ‖x‖ ^ 2) * ‖x‖ ^ 2 := by
    rw [← sum_mul_self_eq_norm_sq, Finset.mul_sum]
    exact Finset.sum_congr rfl fun a _ => by ring
  rw [this]
  field_simp
  norm_num
private theorem inversionMatrix_smul (c : ℝ) (x : TestFunctions.EuclideanFourSpace) (hc : c ≠ 0) :
    inversionMatrix (c • x) = inversionMatrix x := by
  by_cases hx : x = 0
  · subst hx
    simp
  have hn : ‖x‖ ≠ 0 := norm_ne_zero_iff.mpr hx
  ext a b
  simp only [inversionMatrix, Matrix.sub_apply, Matrix.smul_apply, Matrix.vecMulVec_apply, smul_eq_mul,
    norm_smul, Real.norm_eq_abs, mul_pow, sq_abs, PiLp.smul_apply]
  field_simp
theorem inversionMatrix_properties : InversionMatrixProperties := by
  refine ⟨fun x => ?_, inversionMatrix_mul_self, inversionMatrix_det, inversionMatrix_smul, inversionMatrix_zero,
    exteriorSquareTrace_eq, ?_⟩
  · ext a b
    simp [inversionMatrix, Matrix.vecMulVec_apply, Matrix.one_apply, eq_comm, mul_comm]
  · rw [exteriorSquareTrace_eq]
    simp [Matrix.trace_one]
    norm_num
end YangMills.Construction.CyclicFormula
end
