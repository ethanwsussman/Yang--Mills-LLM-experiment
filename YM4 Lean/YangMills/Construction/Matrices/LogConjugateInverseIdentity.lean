import YangMills.Construction.Matrices.LogSeriesTracelessOnUnitDetProof
import YangMills.Construction.Matrices.ExpLogEstimates
import YangMills.Construction.Matrices.LogSeriesConjugateInverse
import YangMills.Construction.Matrices.NormExpLogBasics
import Mathlib
open scoped Matrix.Norms.L2Operator
namespace YangMills.Construction.Matrices.ComplexMatrix2
namespace LogConjInv
noncomputable def logTerm (W : ComplexMatrix2) (n : ℕ) : ComplexMatrix2 :=
  ((n + 1 : ℂ)⁻¹) • W ^ (n + 1)
theorem logSeries_eq_neg_tsum (X : ComplexMatrix2) :
    logSeries X = -∑' n : ℕ, logTerm (1 - X) n := rfl
theorem summable_logTerm {W : ComplexMatrix2} (hW : ‖W‖ < 1) : Summable (logTerm W) := by
  refine Summable.of_norm_bounded (g := fun n : ℕ => ‖W‖ ^ (n + 1)) ?_ ?_
  · exact (summable_nat_add_iff 1).mpr (summable_geometric_of_lt_one (norm_nonneg W) hW)
  · intro n
    have hc : ‖((n + 1 : ℂ)⁻¹)‖ ≤ 1 := by
      rw [norm_inv]
      apply inv_le_one_of_one_le₀
      have h : ‖((n : ℂ) + 1)‖ = (n : ℝ) + 1 := by exact_mod_cast Complex.norm_natCast (n + 1)
      rw [h]
      linarith [(Nat.cast_nonneg n : (0 : ℝ) ≤ n)]
    calc ‖logTerm W n‖ ≤ ‖((n + 1 : ℂ)⁻¹)‖ * ‖W ^ (n + 1)‖ := norm_smul_le _ _
      _ ≤ 1 * ‖W‖ ^ (n + 1) := by
          gcongr
          exact norm_pow_le' W (Nat.succ_pos n)
      _ = ‖W‖ ^ (n + 1) := one_mul _
theorem mul_nonsingInv {W : ComplexMatrix2} (hW : IsUnit W) : W * W⁻¹ = 1 :=
  Matrix.mul_nonsing_inv W ((Matrix.isUnit_iff_isUnit_det W).mp hW)
theorem nonsingInv_mul {W : ComplexMatrix2} (hW : IsUnit W) : W⁻¹ * W = 1 :=
  Matrix.nonsing_inv_mul W ((Matrix.isUnit_iff_isUnit_det W).mp hW)
theorem conj_pow {T : ComplexMatrix2} (hT : IsUnit T) (W : ComplexMatrix2) (n : ℕ) :
    (T⁻¹ * W * T) ^ n = T⁻¹ * W ^ n * T := by
  induction n with
  | zero => simp [nonsingInv_mul hT]
  | succ n ih =>
    rw [pow_succ, ih, pow_succ]
    calc T⁻¹ * W ^ n * T * (T⁻¹ * W * T) = T⁻¹ * W ^ n * (T * T⁻¹) * W * T := by
          simp only [mul_assoc]
      _ = T⁻¹ * (W ^ n * W) * T := by
          rw [mul_nonsingInv hT, mul_one]
          simp only [mul_assoc]
theorem conj_logTerm {T : ComplexMatrix2} (hT : IsUnit T) (W : ComplexMatrix2) (n : ℕ) :
    T⁻¹ * logTerm W n * T = logTerm (T⁻¹ * W * T) n := by
  simp only [logTerm, conj_pow hT, smul_mul_assoc, mul_smul_comm]
theorem hasSum_logTerm_mul_eigen {W R L : ComplexMatrix2} {w : ℂ} (hL : HasSum (logTerm W) L)
    (hR : W * R = w • R) (hw : ‖w‖ < 1) : L * R = (-Complex.log (1 - w)) • R := by
  have hpow : ∀ k : ℕ, W ^ k * R = w ^ k • R := by
    intro k
    induction k with
    | zero => simp
    | succ k ih =>
      rw [pow_succ' W k, mul_assoc, ih, mul_smul_comm, hR, smul_smul, pow_succ w k]
  have hs : HasSum (fun n : ℕ => w ^ (n + 1) / ((n + 1 : ℕ) : ℂ)) (-Complex.log (1 - w)) := by
    have h := (hasSum_nat_add_iff' 1).mpr (Complex.hasSum_taylorSeries_neg_log hw)
    simpa using h
  have h1 := hL.mul_right R
  have h2 := hs.smul_const R
  have hfun : (fun n : ℕ => logTerm W n * R) =
      fun n : ℕ => (w ^ (n + 1) / ((n + 1 : ℕ) : ℂ)) • R := by
    funext n
    simp only [logTerm]
    rw [smul_mul_assoc, hpow, smul_smul]
    congr 1
    push_cast
    rw [div_eq_inv_mul]
  rw [hfun] at h1
  exact h1.unique h2
theorem cayleyHamilton (X : ComplexMatrix2) : X * X = Matrix.trace X • X - X.det • 1 := by apply _root_.YangMills.Construction.Matrices.ComplexMatrix2.TracelessLogSeries.mul_self_eq_trace_smul_sub_det_smul <;> assumption
theorem exists_eigenvalue_pair (X : ComplexMatrix2) : ∃ a b : ℂ, a + b = Matrix.trace X ∧
    a * b = X.det ∧ (X - a • (1 : ComplexMatrix2)) * (X - b • (1 : ComplexMatrix2)) = 0 := by
  obtain ⟨s, hs⟩ := IsAlgClosed.exists_eq_mul_self (Matrix.trace X ^ 2 - 4 * X.det)
  have hsum : (Matrix.trace X + s) / 2 + (Matrix.trace X - s) / 2 = Matrix.trace X := by ring
  have hprod : (Matrix.trace X + s) / 2 * ((Matrix.trace X - s) / 2) = X.det := by
    linear_combination (1 / 4 : ℂ) * hs
  refine ⟨_, _, hsum, hprod, ?_⟩
  generalize (Matrix.trace X + s) / 2 = a at hsum hprod
  generalize (Matrix.trace X - s) / 2 = b at hsum hprod
  have h : (X - a • (1 : ComplexMatrix2)) * (X - b • (1 : ComplexMatrix2)) =
      X * X - (a + b) • X + (a * b) • (1 : ComplexMatrix2) := by
    simp only [sub_mul, mul_sub, smul_mul_assoc, mul_smul_comm, one_mul, mul_one]
    module
  rw [h, cayleyHamilton X, hsum, hprod]
  abel
theorem exists_eigenvector_of_root {X : ComplexMatrix2} {a b : ℂ} (hab : a + b = Matrix.trace X)
    (hd : a * b = X.det) : ∃ v : Fin 2 → ℂ, v ≠ 0 ∧ X.mulVec v = a • v := by
  have hdet : (X - a • (1 : ComplexMatrix2)).det = 0 := by
    rw [Matrix.trace_fin_two] at hab
    rw [Matrix.det_fin_two] at hd
    rw [Matrix.det_fin_two]
    simp only [Matrix.sub_apply, Matrix.smul_apply, Matrix.one_apply_eq, smul_eq_mul, mul_one]
    simp only [Matrix.one_apply_ne (show (0 : Fin 2) ≠ 1 by decide),
      Matrix.one_apply_ne (show (1 : Fin 2) ≠ 0 by decide), mul_zero, sub_zero]
    linear_combination a * hab - hd
  obtain ⟨v, hv, h⟩ := Matrix.exists_mulVec_eq_zero_iff.mpr hdet
  refine ⟨v, hv, ?_⟩
  rw [Matrix.sub_mulVec, Matrix.smul_mulVec, Matrix.one_mulVec, sub_eq_zero] at h
  exact h
def pairSpan (X : ComplexMatrix2) : Submodule ℂ ComplexMatrix2 := Submodule.span ℂ {1, X}
theorem mul_mem_pairSpan {X W W' : ComplexMatrix2} (hW : W ∈ pairSpan X)
    (hW' : W' ∈ pairSpan X) : W * W' ∈ pairSpan X := by
  obtain ⟨a, b, rfl⟩ := Submodule.mem_span_pair.mp hW
  obtain ⟨c, d, rfl⟩ := Submodule.mem_span_pair.mp hW'
  refine Submodule.mem_span_pair.mpr
    ⟨a * c - b * d * X.det, a * d + b * c + b * d * Matrix.trace X, ?_⟩
  simp only [add_mul, mul_add, smul_mul_assoc, mul_smul_comm, one_mul, mul_one, cayleyHamilton X]
  module
theorem commute_of_mem_pairSpan {X W W' : ComplexMatrix2} (hW : W ∈ pairSpan X)
    (hW' : W' ∈ pairSpan X) : Commute W W' := by
  obtain ⟨a, b, rfl⟩ := Submodule.mem_span_pair.mp hW
  obtain ⟨c, d, rfl⟩ := Submodule.mem_span_pair.mp hW'
  have h11 : Commute (1 : ComplexMatrix2) 1 := Commute.refl 1
  have h1X : Commute (1 : ComplexMatrix2) X := Commute.one_left X
  have hX1 : Commute X (1 : ComplexMatrix2) := Commute.one_right X
  have hXX : Commute X X := Commute.refl X
  exact ((h11.smul_left a).smul_right c |>.add_right ((h1X.smul_left a).smul_right d)).add_left
    ((hX1.smul_left b).smul_right c |>.add_right ((hXX.smul_left b).smul_right d))
theorem hasSum_mem_pairSpan {X W L : ComplexMatrix2} (hW : W ∈ pairSpan X)
    (hL : HasSum (logTerm W) L) : L ∈ pairSpan X := by
  have hpow : ∀ n : ℕ, W ^ (n + 1) ∈ pairSpan X := by
    intro n
    induction n with
    | zero => simpa using hW
    | succ n ih => rw [pow_succ]; exact mul_mem_pairSpan ih hW
  have hclosed : IsClosed ((pairSpan X : Submodule ℂ ComplexMatrix2) : Set ComplexMatrix2) :=
    Submodule.closed_of_finiteDimensional _
  exact hclosed.mem_of_tendsto hL.tendsto_sum_nat (Filter.Eventually.of_forall fun s =>
    Submodule.sum_mem _ fun n _ => Submodule.smul_mem _ _ (hpow n))
theorem matExp_of_sq_eq_zero (h₁ : NormExpLogBasics) {N : ComplexMatrix2} (hN : N * N = 0) :
    matExp N = 1 + N := by
  have hs := (h₁.2.1 N).2.1
  have hfin : HasSum (fun n : ℕ => ((n.factorial : ℂ)⁻¹) • N ^ n)
      (∑ n ∈ Finset.range 2, ((n.factorial : ℂ)⁻¹) • N ^ n) := by
    refine hasSum_sum_of_ne_finset_zero fun n hn => ?_
    have h2 : 2 ≤ n := Finset.mem_range.not.mp hn |> not_lt.mp
    obtain ⟨k, rfl⟩ := Nat.exists_eq_add_of_le h2
    rw [pow_add, pow_two, hN, zero_mul, smul_zero]
  rw [hs.unique hfin]
  simp [Finset.sum_range_succ]
theorem logSeries_add_mul_eigen_eq_zero {X S R : ComplexMatrix2} {a : ℂ} (hX : IsUnit X)
    (hX1 : ‖X - 1‖ < 1) (hS : HasSum (logTerm (1 - X⁻¹)) (-S)) (ha0 : a ≠ 0)
    (h1 : ‖1 - a‖ < 1) (h2 : ‖1 - a⁻¹‖ < 1) (hR : (X - a • (1 : ComplexMatrix2)) * R = 0) :
    (logSeries X + S) * R = 0 := by
  have hXR : X * R = a • R := by
    rw [sub_mul, smul_mul_assoc, one_mul, sub_eq_zero] at hR
    exact hR
  have h1R : (1 - X) * R = (1 - a) • R := by rw [sub_mul, one_mul, hXR, sub_smul, one_smul]
  have hback : R = a • (X⁻¹ * R) := by
    calc R = X⁻¹ * (X * R) := by rw [← mul_assoc, nonsingInv_mul hX, one_mul]
      _ = a • (X⁻¹ * R) := by rw [hXR, mul_smul_comm]
  have hXiR : X⁻¹ * R = a⁻¹ • R := ((inv_smul_eq_iff₀ ha0).mpr hback).symm
  have hER : (1 - X⁻¹) * R = (1 - a⁻¹) • R := by
    rw [sub_mul, one_mul, hXiR, sub_smul, one_smul]
  have hn : ‖1 - X‖ < 1 := by rwa [norm_sub_rev]
  have e1 := hasSum_logTerm_mul_eigen (summable_logTerm hn).hasSum h1R h1
  have e2 := hasSum_logTerm_mul_eigen hS hER h2
  rw [sub_sub_cancel] at e1 e2
  have hre : 0 < a.re := by
    have h := (abs_le.mp (Complex.abs_re_le_norm (1 - a))).2
    have h3 := lt_of_le_of_lt h h1
    simp only [Complex.sub_re, Complex.one_re] at h3
    linarith
  have harg : a.arg ≠ Real.pi := fun h => by
    have := (Complex.arg_eq_pi_iff.mp h).1
    linarith
  rw [Complex.log_inv a harg, neg_neg] at e2
  rw [logSeries_eq_neg_tsum, add_mul, neg_mul, e1]
  have e3 : S * R = -(Complex.log a • R) := by
    rw [← e2, neg_mul, neg_neg]
  rw [e3, neg_smul, neg_neg]
  abel
theorem logSeries_add_eq_zero (h₁ : NormExpLogBasics) (h₂ : ExpLogEstimates)
    {X S : ComplexMatrix2} (hX : IsUnit X) (hX1 : ‖X - 1‖ < 1)
    (hS : HasSum (logTerm (1 - X⁻¹)) (-S)) (hexpS : matExp S = X⁻¹)
    (heig : ∀ (a : ℂ) (v : Fin 2 → ℂ), v ≠ 0 → X.mulVec v = a • v → ‖1 - a⁻¹‖ < 1) :
    logSeries X + S = 0 := by
  have hn : ‖1 - X‖ < 1 := by rwa [norm_sub_rev]
  have h1A : (1 : ComplexMatrix2) ∈ pairSpan X := Submodule.subset_span (by simp)
  have hXA : X ∈ pairSpan X := Submodule.subset_span (by simp)
  have hdet : X.det ≠ 0 := ((Matrix.isUnit_iff_isUnit_det X).mp hX).ne_zero
  have hXiA : X⁻¹ ∈ pairSpan X := by
    have hinv : X⁻¹ = (X.det)⁻¹ • (Matrix.trace X • (1 : ComplexMatrix2) - X) := by
      have hq : X * (Matrix.trace X • (1 : ComplexMatrix2) - X) = X.det • (1 : ComplexMatrix2) := by
        rw [mul_sub, mul_smul_comm, mul_one, cayleyHamilton X]
        abel
      calc X⁻¹ = X⁻¹ * ((X.det)⁻¹ • (X.det • (1 : ComplexMatrix2))) := by
            rw [inv_smul_smul₀ hdet, mul_one]
        _ = (X.det)⁻¹ • (X⁻¹ * (X * (Matrix.trace X • (1 : ComplexMatrix2) - X))) := by
            rw [hq, mul_smul_comm]
        _ = _ := by rw [← mul_assoc, nonsingInv_mul hX, one_mul]
    rw [hinv]
    exact Submodule.smul_mem _ _ (Submodule.sub_mem _ (Submodule.smul_mem _ _ h1A) hXA)
  have hLA : logSeries X ∈ pairSpan X := by
    rw [logSeries_eq_neg_tsum]
    exact Submodule.neg_mem _
      (hasSum_mem_pairSpan (Submodule.sub_mem _ h1A hXA) (summable_logTerm hn).hasSum)
  have hSA : S ∈ pairSpan X := by
    have h := hasSum_mem_pairSpan (Submodule.sub_mem _ h1A hXiA) hS
    simpa using Submodule.neg_mem _ h
  have hNA : logSeries X + S ∈ pairSpan X := Submodule.add_mem _ hLA hSA
  have hexpZ : matExp (logSeries X) = X := by
    have h := ((h₂.2.2.2.1 (X - 1) hX1).2.2.2.2)
    simpa using h
  have hexpN : matExp (logSeries X + S) = 1 := by
    have hadd : matExp (logSeries X + S) = matExp (logSeries X) * matExp S := by
      let +nondep : NormedAlgebra ℚ ComplexMatrix2 := .restrictScalars ℚ ℂ ComplexMatrix2
      exact NormedSpace.exp_add_of_commute (commute_of_mem_pairSpan hLA hSA)
    rw [hadd, hexpZ, hexpS, mul_nonsingInv hX]
  obtain ⟨a, b, hab, hd, hq⟩ := exists_eigenvalue_pair X
  have hbound : ∀ (c d : ℂ), c + d = Matrix.trace X → c * d = X.det →
      c ≠ 0 ∧ ‖1 - c‖ < 1 ∧ ‖1 - c⁻¹‖ < 1 := by
    intro c d hcd hcd'
    obtain ⟨v, hv, hXv⟩ := exists_eigenvector_of_root hcd hcd'
    have hc0 : c ≠ 0 := by
      rintro rfl
      apply hdet
      rw [← hcd', zero_mul]
    refine ⟨hc0, ?_, heig c v hv hXv⟩
    have h1v : (1 - X).mulVec v = (1 - c) • v := by
      rw [Matrix.sub_mulVec, Matrix.one_mulVec, hXv, sub_smul, one_smul]
    have hle := h₁.1.2.2.2.2.2.1 (1 - X) (1 - c) v hv h1v
    exact lt_of_le_of_lt hle hn
  obtain ⟨ha0, ha1, ha2⟩ := hbound a b hab hd
  obtain ⟨hb0, hb1, hb2⟩ := hbound b a (by rw [add_comm]; exact hab) (by rw [mul_comm]; exact hd)
  have hcomm : (X - b • (1 : ComplexMatrix2)) * (X - a • (1 : ComplexMatrix2)) = 0 := by
    have h := commute_of_mem_pairSpan (X := X)
      (Submodule.sub_mem _ hXA (Submodule.smul_mem _ b h1A))
      (Submodule.sub_mem _ hXA (Submodule.smul_mem _ a h1A))
    rw [h.eq]
    exact hq
  by_cases hne : a = b
  · subst hne
    by_cases hM : X - a • (1 : ComplexMatrix2) = 0
    · have h := logSeries_add_mul_eigen_eq_zero (R := 1) hX hX1 hS ha0 ha1 ha2
        (by rw [hM, zero_mul])
      simpa using h
    · have hNM := logSeries_add_mul_eigen_eq_zero hX hX1 hS ha0 ha1 ha2 hq
      obtain ⟨p, r, hpr⟩ := Submodule.mem_span_pair.mp hNA
      have hform : logSeries X + S =
          (p + r * a) • (1 : ComplexMatrix2) + r • (X - a • (1 : ComplexMatrix2)) := by
        rw [← hpr, add_smul, smul_sub, smul_smul]
        abel
      have hzero : (p + r * a) • (X - a • (1 : ComplexMatrix2)) = 0 := by
        rw [hform, add_mul, smul_mul_assoc, smul_mul_assoc, hq, smul_zero, add_zero,
          one_mul] at hNM
        exact hNM
      have hc : p + r * a = 0 := (smul_eq_zero.mp hzero).resolve_right hM
      have hN : logSeries X + S = r • (X - a • (1 : ComplexMatrix2)) := by
        rw [hform, hc, zero_smul, zero_add]
      have hsq : (logSeries X + S) * (logSeries X + S) = 0 := by
        rw [hN, smul_mul_assoc, mul_smul_comm, hq, smul_zero, smul_zero]
      have h := matExp_of_sq_eq_zero h₁ hsq
      rw [hexpN] at h
      exact (add_eq_left.mp h.symm)
  · have e1 := logSeries_add_mul_eigen_eq_zero hX hX1 hS ha0 ha1 ha2 hq
    have e2 := logSeries_add_mul_eigen_eq_zero hX hX1 hS hb0 hb1 hb2 hcomm
    have hdiff : (logSeries X + S) * ((a - b) • (1 : ComplexMatrix2)) = 0 := by
      have h : (a - b) • (1 : ComplexMatrix2) =
          (X - b • (1 : ComplexMatrix2)) - (X - a • (1 : ComplexMatrix2)) := by
        rw [sub_smul]
        abel
      rw [h, mul_sub, e1, e2, sub_zero]
    rw [mul_smul_comm, mul_one] at hdiff
    exact (smul_eq_zero.mp hdiff).resolve_left (sub_ne_zero.mpr hne)
end LogConjInv
theorem logSeriesConjugateInverse_holds (h₁ : NormExpLogBasics) (h₂ : ExpLogEstimates) :
    LogSeriesConjugateInverse := by
  intro X T hX hT hX1 hY1
  have hTi := LogConjInv.mul_nonsingInv hT
  have hiT := LogConjInv.nonsingInv_mul hT
  have hiX := LogConjInv.nonsingInv_mul hX
  have hTinv : IsUnit T⁻¹ := (Matrix.isUnit_nonsing_inv_iff).mpr hT
  have hYn : ‖1 - T * X⁻¹ * T⁻¹‖ < 1 := by rwa [norm_sub_rev]
  have hE : T⁻¹ * (1 - T * X⁻¹ * T⁻¹) * T = 1 - X⁻¹ := by
    calc T⁻¹ * (1 - T * X⁻¹ * T⁻¹) * T = T⁻¹ * T - (T⁻¹ * T) * X⁻¹ * (T⁻¹ * T) := by
          simp only [mul_sub, sub_mul, mul_one, mul_assoc]
      _ = 1 - X⁻¹ := by rw [hiT, one_mul, mul_one]
  have hS : HasSum (LogConjInv.logTerm (1 - X⁻¹))
      (-(T⁻¹ * logSeries (T * X⁻¹ * T⁻¹) * T)) := by
    have h := ((LogConjInv.summable_logTerm hYn).hasSum.mul_left T⁻¹).mul_right T
    have hfun : (fun n : ℕ => T⁻¹ * LogConjInv.logTerm
        (1 - T * X⁻¹ * T⁻¹) n * T) = LogConjInv.logTerm (1 - X⁻¹) := by
      funext n
      rw [LogConjInv.conj_logTerm hT, hE]
    rw [hfun] at h
    rw [LogConjInv.logSeries_eq_neg_tsum (T * X⁻¹ * T⁻¹), mul_neg, neg_mul, neg_neg]
    exact h
  have hexpY : matExp (logSeries (T * X⁻¹ * T⁻¹)) = T * X⁻¹ * T⁻¹ := by
    have h := (h₂.2.2.2.1 (T * X⁻¹ * T⁻¹ - 1) hY1).2.2.2.2
    simpa using h
  have hexpS : matExp (T⁻¹ * logSeries (T * X⁻¹ * T⁻¹) * T) = X⁻¹ := by
    have h := (h₁.2.1 (logSeries (T * X⁻¹ * T⁻¹))).2.2.2.2.2.2 T⁻¹ hTinv
    rw [Matrix.nonsing_inv_nonsing_inv T ((Matrix.isUnit_iff_isUnit_det T).mp hT), hexpY] at h
    rw [← h]
    calc T⁻¹ * (T * X⁻¹ * T⁻¹) * T = (T⁻¹ * T) * X⁻¹ * (T⁻¹ * T) := by simp only [mul_assoc]
      _ = X⁻¹ := by rw [hiT, one_mul, mul_one]
  have heig : ∀ (a : ℂ) (v : Fin 2 → ℂ), v ≠ 0 → X.mulVec v = a • v → ‖1 - a⁻¹‖ < 1 := by
    intro a v hv hXv
    have ha0 : a ≠ 0 := by
      rintro rfl
      apply hv
      have h : (X⁻¹ * X).mulVec v = 0 := by
        rw [← Matrix.mulVec_mulVec, hXv, zero_smul, Matrix.mulVec_zero]
      rwa [hiX, Matrix.one_mulVec] at h
    have hXiv : X⁻¹.mulVec v = a⁻¹ • v := by
      have h : v = a • X⁻¹.mulVec v := by
        calc v = (X⁻¹ * X).mulVec v := by rw [hiX, Matrix.one_mulVec]
          _ = X⁻¹.mulVec (a • v) := by rw [← Matrix.mulVec_mulVec, hXv]
          _ = a • X⁻¹.mulVec v := Matrix.mulVec_smul _ _ _
      exact ((inv_smul_eq_iff₀ ha0).mpr h).symm
    have hTv : T.mulVec v ≠ 0 := by
      intro h0
      apply hv
      have h : (T⁻¹ * T).mulVec v = 0 := by
        rw [← Matrix.mulVec_mulVec, h0, Matrix.mulVec_zero]
      rwa [hiT, Matrix.one_mulVec] at h
    have hYv : (1 - T * X⁻¹ * T⁻¹).mulVec (T.mulVec v) = (1 - a⁻¹) • T.mulVec v := by
      rw [Matrix.sub_mulVec, Matrix.one_mulVec, Matrix.mulVec_mulVec]
      have h : T * X⁻¹ * T⁻¹ * T = T * X⁻¹ := by rw [mul_assoc, hiT, mul_one]
      rw [h, ← Matrix.mulVec_mulVec, hXiv, Matrix.mulVec_smul, sub_smul, one_smul]
    exact lt_of_le_of_lt (h₁.1.2.2.2.2.2.1 _ _ _ hTv hYv) hYn
  have hN := LogConjInv.logSeries_add_eq_zero h₁ h₂ hX hX1 hS hexpS heig
  have hS' : T⁻¹ * logSeries (T * X⁻¹ * T⁻¹) * T = -logSeries X :=
    eq_neg_of_add_eq_zero_right hN
  calc logSeries (T * X⁻¹ * T⁻¹) = (T * T⁻¹) * logSeries (T * X⁻¹ * T⁻¹) * (T * T⁻¹) := by
        rw [hTi, one_mul, mul_one]
    _ = T * (T⁻¹ * logSeries (T * X⁻¹ * T⁻¹) * T) * T⁻¹ := by simp only [mul_assoc]
    _ = -(T * logSeries X * T⁻¹) := by rw [hS', mul_neg, neg_mul]
end YangMills.Construction.Matrices.ComplexMatrix2
