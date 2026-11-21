import YangMills.Construction.FormsOnATorus.DeterminantNearOne
import Mathlib
set_option autoImplicit false
noncomputable section
open Matrix
namespace YangMills.Construction.MatrixDeterminants
attribute [local instance] Matrix.frobeniusNormedAddCommGroup Matrix.frobeniusNormedRing
private lemma frobenius_norm_sq_eq_sum {α : Type} [Fintype α] (A : Matrix α α ℝ) :
    ‖A‖ ^ 2 = ∑ i, ∑ j, A i j ^ 2 := by
  have h0 : 0 ≤ ∑ i, ∑ j, ‖A i j‖ ^ (2 : ℝ) :=
    Finset.sum_nonneg fun i _ => Finset.sum_nonneg fun j _ => by positivity
  rw [Matrix.frobenius_norm_def, ← Real.rpow_natCast, ← Real.rpow_mul h0]
  norm_num
private lemma abs_log_one_add_le {t : ℝ} (ht : |t| ≤ 1 / 2) : |Real.log (1 + t)| ≤ 2 * |t| := by
  have hlo := (abs_le.mp ht).1
  have hpos : 0 < 1 + t := by linarith
  have h1 : Real.log (1 + t) ≤ t := by
    have := Real.log_le_sub_one_of_pos hpos
    linarith
  have h2 : 1 - (1 + t)⁻¹ ≤ Real.log (1 + t) := Real.one_sub_inv_le_log_of_pos hpos
  have h3 : -(2 * |t|) ≤ 1 - (1 + t)⁻¹ := by
    have he : 1 - (1 + t)⁻¹ = t / (1 + t) := by
      field_simp
      ring
    rw [he, le_div_iff₀ hpos]
    rcases abs_cases t with ⟨h, h'⟩ | ⟨h, h'⟩ <;> rw [h] <;> nlinarith
  rw [abs_le]
  constructor
  · linarith
  · linarith [le_abs_self t, abs_nonneg t]
theorem logDetOneAddBound_holds : LogDetOneAddBound := by
  intro α _ _ G s hs hs8 hG
  set H : Matrix α α ℝ := G + Gᵀ + Gᵀ * G with hHdef
  have hA : (1 + G)ᵀ * (1 + G) = 1 + H := by
    simp only [hHdef, Matrix.transpose_add, Matrix.transpose_one, Matrix.add_mul, Matrix.mul_add,
      Matrix.one_mul, Matrix.mul_one]
    abel
  have hsym : Hᵀ = H := by
    simp only [hHdef, Matrix.transpose_add, Matrix.transpose_mul, Matrix.transpose_transpose]
    abel
  have hH : H.IsHermitian := by
    rw [Matrix.IsHermitian, Matrix.conjTranspose_eq_transpose_of_trivial]
    exact hsym
  have hGn : ‖G‖ ≤ s := by
    have : ‖G‖ ^ 2 ≤ s ^ 2 := by rw [frobenius_norm_sq_eq_sum]; exact hG
    exact (pow_le_pow_iff_left₀ (norm_nonneg _) hs (by norm_num)).mp this
  have hGt : ‖Gᵀ‖ = ‖G‖ := by
    have : ‖Gᵀ‖ ^ 2 = ‖G‖ ^ 2 := by
      rw [frobenius_norm_sq_eq_sum, frobenius_norm_sq_eq_sum, Finset.sum_comm]
      rfl
    exact (pow_left_inj₀ (norm_nonneg _) (norm_nonneg _) (by norm_num)).mp this
  have hHn : ‖H‖ ≤ 3 * s := by
    calc ‖H‖ ≤ ‖G + Gᵀ‖ + ‖Gᵀ * G‖ := norm_add_le _ _
      _ ≤ (‖G‖ + ‖Gᵀ‖) + ‖Gᵀ‖ * ‖G‖ := add_le_add (norm_add_le _ _) (norm_mul_le _ _)
      _ ≤ (s + s) + s * s := by
          rw [hGt]
          have := mul_le_mul hGn hGn (norm_nonneg _) hs
          linarith
      _ ≤ 3 * s := by nlinarith
  set U : Matrix α α ℝ := (hH.eigenvectorUnitary : Matrix α α ℝ) with hU
  set lam : α → ℝ := hH.eigenvalues with hlam
  set Dg : Matrix α α ℝ := diagonal lam with hDg
  have hsp : H = U * Dg * star U := by
    have h := hH.spectral_theorem
    rw [Unitary.conjStarAlgAut_apply] at h
    simpa [hU, hDg, hlam, Function.comp_def] using h
  have hUs : star U * U = 1 := Unitary.coe_star_mul_self hH.eigenvectorUnitary
  have hUs' : U * star U = 1 := Unitary.coe_mul_star_self hH.eigenvectorUnitary
  have hdU : (star U).det * U.det = 1 := by
    rw [← Matrix.det_mul, hUs, Matrix.det_one]
  have h1H : 1 + H = U * (1 + Dg) * star U := by
    calc 1 + H = U * star U + U * Dg * star U := by rw [hUs', ← hsp]
      _ = U * (1 + Dg) * star U := by noncomm_ring
  have hdet : (1 + H).det = ∏ i, (1 + lam i) := by
    have hd : (1 : Matrix α α ℝ) + Dg = diagonal fun i => 1 + lam i := by
      ext i j
      by_cases hij : i = j
      · subst hij
        simp [hDg]
      · simp [hDg, hij]
    rw [h1H, Matrix.det_mul, Matrix.det_mul, hd, Matrix.det_diagonal]
    calc U.det * (∏ i, (1 + lam i)) * (star U).det
        = (∏ i, (1 + lam i)) * ((star U).det * U.det) := by ring
      _ = _ := by rw [hdU, mul_one]
  have hsq : ∑ i, lam i ^ 2 = ‖H‖ ^ 2 := by
    have hHH : H * H = U * (Dg * Dg) * star U := by
      calc H * H = U * Dg * (star U * U) * Dg * star U := by
            rw [hsp]
            noncomm_ring
        _ = U * (Dg * Dg) * star U := by
            rw [hUs]
            noncomm_ring
    have htr : (H * H).trace = ∑ i, lam i ^ 2 := by
      rw [hHH, Matrix.trace_mul_comm, ← mul_assoc, ← mul_assoc, hUs, one_mul, hDg,
        Matrix.diagonal_mul_diagonal, Matrix.trace_diagonal]
      exact Finset.sum_congr rfl fun i _ => by ring
    rw [← htr, frobenius_norm_sq_eq_sum, Matrix.trace]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [Matrix.diag_apply, Matrix.mul_apply]
    refine Finset.sum_congr rfl fun j _ => ?_
    have : H j i = H i j := congrFun (congrFun hsym i) j
    rw [this]
    ring
  have hlam3 : ∀ i, |lam i| ≤ 3 * s := by
    intro i
    have h1 : lam i ^ 2 ≤ ∑ j, lam j ^ 2 :=
      Finset.single_le_sum (f := fun j => lam j ^ 2) (fun j _ => by positivity) (Finset.mem_univ i)
    have h2 : lam i ^ 2 ≤ (3 * s) ^ 2 := by
      rw [hsq] at h1
      exact h1.trans (pow_le_pow_left₀ (norm_nonneg _) hHn 2)
    exact abs_le_of_sq_le_sq h2 (by positivity)
  have hlam2 : ∀ i, |lam i| ≤ 1 / 2 := fun i => (hlam3 i).trans (by linarith)
  have hpos : ∀ i, 0 < 1 + lam i := fun i => by
    have := (abs_le.mp (hlam2 i)).1
    linarith
  have hdsq : (1 + G).det ^ 2 = ∏ i, (1 + lam i) := by
    rw [← hdet, ← hA, Matrix.det_mul, Matrix.det_transpose]
    ring
  have hprod : 0 < ∏ i, (1 + lam i) := Finset.prod_pos fun i _ => hpos i
  have hne : (1 + G).det ≠ 0 := by
    intro h
    rw [h] at hdsq
    norm_num at hdsq
    exact hprod.ne' hdsq.symm
  refine ⟨hne, ?_⟩
  have hlog : 2 * Real.log (abs (1 + G).det) = ∑ i, Real.log (1 + lam i) := by
    rw [← Real.log_prod (fun i _ => (hpos i).ne'), ← hdsq, Real.log_abs, Real.log_pow]
    norm_num
  have hsum : |∑ i, Real.log (1 + lam i)| ≤ 2 * ∑ i, |lam i| := by
    calc |∑ i, Real.log (1 + lam i)| ≤ ∑ i, |Real.log (1 + lam i)| := Finset.abs_sum_le_sum_abs _ _
      _ ≤ ∑ i, 2 * |lam i| := Finset.sum_le_sum fun i _ => abs_log_one_add_le (hlam2 i)
      _ = 2 * ∑ i, |lam i| := by rw [Finset.mul_sum]
  have hcs : ∑ i, |lam i| ≤ Real.sqrt (Fintype.card α) * (3 * s) := by
    have h1 : (∑ i, |lam i|) ^ 2 ≤ (Fintype.card α : ℝ) * ∑ i, |lam i| ^ 2 := by
      simpa using sq_sum_le_card_mul_sum_sq (s := Finset.univ) (f := fun i => |lam i|)
    have h2 : ∑ i, |lam i| ^ 2 ≤ (3 * s) ^ 2 := by
      simp only [sq_abs]
      rw [hsq]
      exact pow_le_pow_left₀ (norm_nonneg _) hHn 2
    have h3 : (∑ i, |lam i|) ^ 2 ≤ (Real.sqrt (Fintype.card α) * (3 * s)) ^ 2 := by
      rw [mul_pow, Real.sq_sqrt (by positivity)]
      exact h1.trans (mul_le_mul_of_nonneg_left h2 (by positivity))
    exact abs_le_of_sq_le_sq' h3 (by positivity) |>.2
  have : |Real.log (abs (1 + G).det)| = |∑ i, Real.log (1 + lam i)| / 2 := by
    rw [← hlog, abs_mul]
    norm_num
  rw [this]
  nlinarith
end YangMills.Construction.MatrixDeterminants
end
