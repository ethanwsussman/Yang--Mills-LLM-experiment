import YangMills.Construction.Matrices.DeterminantDerivative
import Mathlib
set_option autoImplicit false
noncomputable section
namespace YangMills.Construction.Matrices.Determinant
variable {n : Type} [Fintype n] [DecidableEq n]
private theorem hasDerivWithinAt_det_of_entries (I : Set ℝ) (M M' : ℝ → Matrix n n ℂ) (t : ℝ)
    (hM : ∀ i j, HasDerivWithinAt (fun s => M s i j) (M' t i j) I t) :
    HasDerivWithinAt (fun s => (M s).det) ((M t).adjugate * M' t).trace I t := by
  have hval : ((M t).adjugate * M' t).trace =
      ∑ i, ∑ σ : Equiv.Perm n, ((Equiv.Perm.sign σ : ℤ) : ℂ) *
        ((∏ j ∈ Finset.univ.erase i, M t (σ j) j) * M' t (σ i) i) := by
    simp only [Matrix.trace, Matrix.diag_apply]
    refine Finset.sum_congr rfl fun i _ => ?_
    have h1 : ((M t).adjugate * M' t) i i = Matrix.cramer (M t) (fun k => M' t k i) i := by
      rw [Matrix.cramer_eq_adjugate_mulVec]
      simp [Matrix.mul_apply, Matrix.mulVec, dotProduct]
    rw [h1, Matrix.cramer_apply, Matrix.det_apply']
    refine Finset.sum_congr rfl fun σ _ => ?_
    congr 1
    rw [← Finset.prod_erase_mul Finset.univ _ (Finset.mem_univ i)]
    congr 1
    · refine Finset.prod_congr rfl fun j hj => ?_
      rw [Matrix.updateCol_apply, if_neg (Finset.ne_of_mem_erase hj)]
    · simp
  have hdet : (fun s => (M s).det) =
      fun s => ∑ σ : Equiv.Perm n, ((Equiv.Perm.sign σ : ℤ) : ℂ) * ∏ i, M s (σ i) i := by
    funext s
    rw [Matrix.det_apply']
  rw [hval, Finset.sum_comm, hdet]
  refine HasDerivWithinAt.fun_sum fun σ _ => ?_
  rw [← Finset.mul_sum]
  refine HasDerivWithinAt.const_mul _ ?_
  have hp := HasDerivWithinAt.fun_finsetProd (u := Finset.univ)
    (f := fun i s => M s (σ i) i) (f' := fun i => M' t (σ i) i) (fun i _ => hM (σ i) i)
  simpa [smul_eq_mul] using hp
open scoped Matrix.Norms.Operator in
private theorem det_exp_eq_exp_trace (K : Matrix n n ℂ) :
    (NormedSpace.exp K).det = Complex.exp K.trace := by
  have hent : ∀ (t : ℝ) (i j : n), HasDerivWithinAt
      (fun s : ℝ => NormedSpace.exp (s • K) i j) ((NormedSpace.exp (t • K) * K) i j) Set.univ t := by
    intro t i j
    let L : Matrix n n ℂ →L[ℝ] ℂ :=
      LinearMap.toContinuousLinearMap (Matrix.entryLinearMap ℝ ℂ i j)
    exact (L.hasFDerivAt.comp_hasDerivAt t (hasDerivAt_exp_smul_const K t)).hasDerivWithinAt
  have hder : ∀ t : ℝ, HasDerivAt (fun s : ℝ => (NormedSpace.exp (s • K)).det)
      ((NormedSpace.exp (t • K)).det * K.trace) t := by
    intro t
    have h := hasDerivWithinAt_det_of_entries Set.univ (fun s : ℝ => NormedSpace.exp (s • K))
      (fun s : ℝ => NormedSpace.exp (s • K) * K) t (hent t)
    rw [hasDerivWithinAt_univ, ← Matrix.mul_assoc, Matrix.adjugate_mul, Matrix.smul_mul,
      Matrix.one_mul, Matrix.trace_smul, smul_eq_mul] at h
    exact h
  have hexp : ∀ t : ℝ, HasDerivAt (fun s : ℝ => Complex.exp (-(s : ℂ) * K.trace))
      (Complex.exp (-(t : ℂ) * K.trace) * (-K.trace)) t := by
    intro t
    have h : HasDerivAt (fun s : ℝ => -(s : ℂ) * K.trace) (-K.trace) t := by
      simpa using (Complex.ofRealCLM.hasDerivAt (x := t)).neg.mul_const K.trace
    exact h.cexp
  have hzero : ∀ t : ℝ, HasDerivAt
      (fun s : ℝ => (NormedSpace.exp (s • K)).det * Complex.exp (-(s : ℂ) * K.trace)) 0 t := by
    intro t
    have h := (hder t).fun_mul (hexp t)
    have h0 : (NormedSpace.exp (t • K)).det * K.trace * Complex.exp (-(t : ℂ) * K.trace) +
        (NormedSpace.exp (t • K)).det * (Complex.exp (-(t : ℂ) * K.trace) * -K.trace) = 0 := by
      ring
    rwa [h0] at h
  have hconst := is_const_of_deriv_eq_zero (𝕜 := ℝ)
    (fun t => (hzero t).differentiableAt) (fun t => (hzero t).deriv) 1 0
  simp only [one_smul, zero_smul, NormedSpace.exp_zero, Matrix.det_one, Complex.ofReal_one,
    Complex.ofReal_zero, neg_zero, zero_mul, Complex.exp_zero, mul_one, neg_mul, one_mul] at hconst
  rw [Complex.exp_neg] at hconst
  field_simp [Complex.exp_ne_zero] at hconst
  exact hconst
theorem jacobiDeterminantFormula : JacobiDeterminantFormula := by
  intro n _ _
  refine ⟨fun I M M' _ hU hd t ht => ?_, det_exp_eq_exp_trace⟩
  have hu : IsUnit (M t).det := (Matrix.isUnit_iff_isUnit_det _).1 (hU t ht)
  have h := hasDerivWithinAt_det_of_entries I M M' t (hd t ht)
  convert h using 1
  rw [Matrix.inv_def, Matrix.smul_mul, Matrix.trace_smul, Ring.inverse_eq_inv, smul_eq_mul,
    mul_inv_cancel_left₀ hu.ne_zero]
end YangMills.Construction.Matrices.Determinant
end
