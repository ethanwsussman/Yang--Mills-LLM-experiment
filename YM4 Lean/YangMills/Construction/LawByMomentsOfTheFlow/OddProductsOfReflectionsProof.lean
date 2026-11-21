import YangMills.Construction.LawByMomentsOfTheFlow.FactsOfAReflection
import YangMills.Construction.LawByMomentsOfTheFlow.OddProductsOfReflections
import Mathlib
set_option autoImplicit false
noncomputable section
namespace YangMills.Construction
namespace CyclicFormula
private theorem det_fin_four_expand (M : Matrix (Fin 4) (Fin 4) ℝ) : M.det =
    M 0 0 * M 1 1 * M 2 2 * M 3 3 - M 0 0 * M 1 1 * M 2 3 * M 3 2 - M 0 0 * M 1 2 * M 2 1 * M 3 3 + M 0 0 * M 1 2 * M 2 3 * M 3 1 - M 0 0 * M 1 3 * M 2 2 * M 3 1 + M 0 0 * M 1 3 * M 2 1 * M 3 2 - M 0 1 * M 1 0 * M 2 2 * M 3 3 + M 0 1 * M 1 0 * M 2 3 * M 3 2 + M 0 1 * M 1 2 * M 2 0 * M 3 3 - M 0 1 * M 1 2 * M 2 3 * M 3 0 + M 0 1 * M 1 3 * M 2 2 * M 3 0 - M 0 1 * M 1 3 * M 2 0 * M 3 2 - M 0 2 * M 1 1 * M 2 0 * M 3 3 + M 0 2 * M 1 1 * M 2 3 * M 3 0 + M 0 2 * M 1 0 * M 2 1 * M 3 3 - M 0 2 * M 1 0 * M 2 3 * M 3 1 + M 0 2 * M 1 3 * M 2 0 * M 3 1 - M 0 2 * M 1 3 * M 2 1 * M 3 0 - M 0 3 * M 1 1 * M 2 2 * M 3 0 + M 0 3 * M 1 1 * M 2 0 * M 3 2 + M 0 3 * M 1 2 * M 2 1 * M 3 0 - M 0 3 * M 1 2 * M 2 0 * M 3 1 + M 0 3 * M 1 0 * M 2 2 * M 3 1 - M 0 3 * M 1 0 * M 2 1 * M 3 2 := by
  rw [Matrix.det_succ_row_zero]
  simp only [Fin.sum_univ_four, Matrix.det_fin_three, Matrix.submatrix_apply]
  simp [Fin.succAbove]
  ring
private theorem det_one_sub_add_det_one_add (A : Matrix (Fin 4) (Fin 4) ℝ) :
    (1 - A).det + (1 + A).det =
      2 + ((Matrix.trace A) ^ 2 - Matrix.trace (A * A)) + 2 * A.det := by
  rw [det_fin_four_expand, det_fin_four_expand (1 + A), det_fin_four_expand A]
  simp only [Matrix.trace, Matrix.diag, Matrix.mul_apply, Fin.sum_univ_four, Matrix.sub_apply, Matrix.add_apply,
    Matrix.one_apply]
  simp
  ring
private theorem trace_sq_sub_trace_mul_self_of_improper (A : Matrix (Fin 4) (Fin 4) ℝ)
    (hA : A * A.transpose = 1) (hdet : A.det = -1) :
    ((Matrix.trace A) ^ 2 - Matrix.trace (A * A)) = 0 := by
  have hsub : (1 - A).det = 0 := by
    have e : (1 : Matrix (Fin 4) (Fin 4) ℝ) - A = A * (A.transpose - 1) := by
      rw [Matrix.mul_sub, hA, Matrix.mul_one]
    have e2 : (A.transpose - 1).det = (1 - A).det := by
      have : A.transpose - 1 = -(1 - A).transpose := by
        simp [Matrix.transpose_sub]
      rw [this, Matrix.det_neg, Matrix.det_transpose]
      norm_num
    have := congrArg Matrix.det e
    rw [Matrix.det_mul, hdet, e2] at this
    linarith
  have hadd : (1 + A).det = 0 := by
    have e : (1 : Matrix (Fin 4) (Fin 4) ℝ) + A = A * (A.transpose + 1) := by
      rw [Matrix.mul_add, hA, Matrix.mul_one]
    have e2 : (A.transpose + 1).det = (1 + A).det := by
      have : A.transpose + 1 = (1 + A).transpose := by
        simp [Matrix.transpose_add, add_comm]
      rw [this, Matrix.det_transpose]
    have := congrArg Matrix.det e
    rw [Matrix.det_mul, hdet, e2] at this
    linarith
  have := det_one_sub_add_det_one_add A
  rw [hsub, hadd, hdet] at this
  linarith
theorem exteriorSquareTraceOfOddInversionProduct_holds (hF : InversionMatrixProperties) :
    ExteriorSquareTraceOfOddInversionProduct := by
  obtain ⟨hT, hI, hD, -, -, hE, -⟩ := hF
  have hzero : ∀ A : Matrix (Fin 4) (Fin 4) ℝ, A * A.transpose = 1 → A.det = -1 →
      exteriorSquareTrace A = 0 := by
    intro A hA hdet
    rw [hE, trace_sq_sub_trace_mul_self_of_improper A hA hdet]
    simp
  refine ⟨hzero, fun l hl hne => ?_⟩
  have key : ∀ l : List TestFunctions.EuclideanFourSpace, (∀ x ∈ l, x ≠ 0) →
      (l.map inversionMatrix).prod * (l.map inversionMatrix).prod.transpose = 1 ∧
        (l.map inversionMatrix).prod.det = (-1) ^ l.length := by
    intro l
    induction l with
    | nil => simp
    | cons x t ih =>
      intro h
      obtain ⟨h1, h2⟩ := ih fun y hy => h y (List.mem_cons_of_mem _ hy)
      simp only [List.map_cons, List.prod_cons, List.length_cons, Matrix.det_mul, Matrix.transpose_mul]
      refine ⟨?_, ?_⟩
      · calc inversionMatrix x * (t.map inversionMatrix).prod *
              ((t.map inversionMatrix).prod.transpose * (inversionMatrix x).transpose)
            = inversionMatrix x * ((t.map inversionMatrix).prod * (t.map inversionMatrix).prod.transpose) *
                (inversionMatrix x).transpose := by simp only [Matrix.mul_assoc]
          _ = 1 := by rw [h1, Matrix.mul_one, hT, hI]
      · rw [h2, hD x (h x List.mem_cons_self), pow_succ]
        ring
  obtain ⟨h1, h2⟩ := key l hne
  exact hzero _ h1 (by rw [h2, hl.neg_one_pow])
end CyclicFormula
end YangMills.Construction
end
