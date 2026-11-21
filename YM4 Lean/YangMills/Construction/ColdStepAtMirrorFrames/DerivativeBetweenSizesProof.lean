import YangMills.Construction.ColdStepAtMirrorFrames.DerivativeBetweenSizes
import Mathlib
set_option autoImplicit false
noncomputable section
namespace YangMills.Construction.ColdStepAtMirrorFrames
namespace LandauKolmogorov
theorem taylor_remainder_le_of_hasDerivAt_chain (τ M : ℝ) (hM : 0 ≤ M) (p : ℕ) : ∀ (g : ℕ → ℝ → ℝ),
    (∀ i, i < p → ∀ s, |s| ≤ τ → HasDerivAt (g i) (g (i + 1) s) s) →
    (∀ s, |s| ≤ τ → |g p s| ≤ M) →
    ∀ s, |s| ≤ τ → |g 0 s - ∑ i ∈ Finset.range p, g i 0 * s ^ i / i.factorial| ≤ M * |s| ^ p := by
  induction p with
  | zero =>
    intro g _ hbound s hs
    simpa using hbound s hs
  | succ p ih =>
    intro g hderiv hbound s hs
    have ih' := ih (fun i => g (i + 1)) (fun i hi t ht => hderiv (i + 1) (by omega) t ht) hbound
    set R : ℝ → ℝ := fun t => g 0 t - ∑ i ∈ Finset.range (p + 1), g i 0 * t ^ i / i.factorial
      with hR
    set R' : ℝ → ℝ := fun t => g 1 t - ∑ i ∈ Finset.range p, g (i + 1) 0 * t ^ i / i.factorial
      with hR'
    have hder : ∀ t, |t| ≤ τ → HasDerivAt R (R' t) t := by
      intro t ht
      have h1 := hderiv 0 (by omega) t ht
      have h2 : HasDerivAt (fun t : ℝ => ∑ i ∈ Finset.range (p + 1), g i 0 * t ^ i / i.factorial)
          (∑ i ∈ Finset.range p, g (i + 1) 0 * t ^ i / i.factorial) t := by
        have e : (fun t : ℝ => ∑ i ∈ Finset.range (p + 1), g i 0 * t ^ i / i.factorial) =
            fun t : ℝ => (∑ i ∈ Finset.range p, g (i + 1) 0 * t ^ (i + 1) / (i + 1).factorial) +
              g 0 0 := by
          funext t
          rw [Finset.sum_range_succ']
          simp
        rw [e]
        apply HasDerivAt.add_const
        apply HasDerivAt.fun_sum
        intro i _
        have h3 := ((hasDerivAt_pow (i + 1) t).const_mul (g (i + 1) 0)).div_const
          ((i + 1).factorial : ℝ)
        refine HasDerivAt.congr_deriv h3 ?_
        rw [Nat.factorial_succ]
        have : ((i.factorial : ℝ)) ≠ 0 := by exact_mod_cast (Nat.factorial_pos i).ne'
        have h5 : ((i : ℝ) + 1) ≠ 0 := by positivity
        push_cast
        field_simp
      exact h1.sub h2
    have hle : ∀ t ∈ Set.Icc (-|s|) |s|, ‖R' t‖ ≤ M * |s| ^ p := by
      intro t ht
      have ht' : |t| ≤ |s| := abs_le.mpr ht
      have := ih' t (ht'.trans hs)
      rw [Real.norm_eq_abs]
      calc |R' t| ≤ M * |t| ^ p := this
        _ ≤ M * |s| ^ p := by gcongr
    have hmvt := Convex.norm_image_sub_le_of_norm_hasDerivWithin_le (f := R) (f' := R')
      (s := Set.Icc (-|s|) |s|) (x := 0) (y := s) (C := M * |s| ^ p)
      (fun t ht => (hder t ((abs_le.mpr ht).trans hs)).hasDerivWithinAt) hle
      (convex_Icc _ _) ⟨by simp, abs_nonneg s⟩ ⟨neg_abs_le s, le_abs_self s⟩
    have h0 : R 0 = 0 := by
      simp only [hR]
      rw [Finset.sum_range_succ']
      simp
    rw [h0, sub_zero, sub_zero, Real.norm_eq_abs, Real.norm_eq_abs] at hmvt
    calc |R s| ≤ M * |s| ^ p * |s| := hmvt
      _ = M * |s| ^ (p + 1) := by ring
theorem exists_coeff_le_of_values_at_nodes (p : ℕ) (hp : 0 < p) : ∃ K : ℝ, 0 ≤ K ∧ ∀ (a : Fin p → ℝ) (B : ℝ),
    (∀ l : Fin p, |∑ i : Fin p, a i * ((l : ℝ) / p) ^ (i : ℕ)| ≤ B) → ∀ i, |a i| ≤ K * B := by
  set ξ : Fin p → ℝ := fun l => (l : ℝ) / p with hξ
  have hinj : Function.Injective ξ := by
    intro l l' h
    have hp' : (p : ℝ) ≠ 0 := by positivity
    have : (l : ℝ) = l' := by
      simp only [hξ] at h
      field_simp at h
      exact h
    exact Fin.ext (by exact_mod_cast this)
  set V := Matrix.vandermonde ξ with hV
  have hdet : V.det ≠ 0 := Matrix.det_vandermonde_ne_zero_iff.mpr hinj
  have hunit : IsUnit V.det := isUnit_iff_ne_zero.mpr hdet
  refine ⟨∑ i, ∑ j, |V⁻¹ i j|, by positivity, fun a B hB i => ?_⟩
  have hB0 : 0 ≤ B := (abs_nonneg _).trans (hB ⟨0, hp⟩)
  have hval : ∀ l, V.mulVec a l = ∑ i : Fin p, a i * ((l : ℝ) / p) ^ (i : ℕ) := by
    intro l
    simp only [Matrix.mulVec, dotProduct, hV, Matrix.vandermonde_apply, hξ]
    exact Finset.sum_congr rfl fun i _ => mul_comm _ _
  have hinv : a = V⁻¹.mulVec (V.mulVec a) := by
    rw [Matrix.mulVec_mulVec, Matrix.nonsing_inv_mul _ hunit, Matrix.one_mulVec]
  have h1 : a i = ∑ j, V⁻¹ i j * V.mulVec a j := by
    conv_lhs => rw [hinv]
    rfl
  rw [h1]
  calc |∑ j, V⁻¹ i j * V.mulVec a j| ≤ ∑ j, |V⁻¹ i j * V.mulVec a j| :=
        Finset.abs_sum_le_sum_abs _ _
    _ ≤ ∑ j, |V⁻¹ i j| * B := by
        apply Finset.sum_le_sum
        intro j _
        rw [abs_mul, hval j]
        exact mul_le_mul_of_nonneg_left (hB j) (abs_nonneg _)
    _ = (∑ j, |V⁻¹ i j|) * B := by rw [Finset.sum_mul]
    _ ≤ (∑ i, ∑ j, |V⁻¹ i j|) * B := by
        apply mul_le_mul_of_nonneg_right _ hB0
        exact Finset.single_le_sum (f := fun i => ∑ j, |V⁻¹ i j|)
          (fun i _ => by positivity) (Finset.mem_univ i)
theorem exists_step_size (p j : ℕ) (hj : j < p) (τ₀ M₀ Mp : ℝ) (hτ : 0 < τ₀) (hM : 0 < M₀) (hMp : 0 ≤ Mp) :
    ∃ h : ℝ, 0 < h ∧ h ≤ τ₀ ∧ Mp * h ^ p ≤ M₀ ∧
      M₀ / h ^ j ≤ M₀ / τ₀ ^ j + M₀ ^ (1 - (j : ℝ) / p) * Mp ^ ((j : ℝ) / p) := by
  have hp : 0 < p := by omega
  by_cases hc : Mp * τ₀ ^ p ≤ M₀
  · refine ⟨τ₀, hτ, le_rfl, hc, ?_⟩
    have : 0 ≤ M₀ ^ (1 - (j : ℝ) / p) * Mp ^ ((j : ℝ) / p) := by positivity
    linarith
  · push Not at hc
    have hMp0 : 0 < Mp := by
      rcases hMp.lt_or_eq with h | h
      · exact h
      · rw [← h] at hc
        simp at hc
        linarith
    set r : ℝ := M₀ / Mp with hr
    have hr0 : 0 < r := by positivity
    set h : ℝ := r ^ ((p : ℝ)⁻¹) with hh
    have hh0 : 0 < h := by positivity
    have hpow : h ^ p = r := Real.rpow_inv_natCast_pow hr0.le hp.ne'
    have hlt : r < τ₀ ^ p := by
      rw [hr, div_lt_iff₀ hMp0]
      linarith
    have hle : h ≤ τ₀ := by
      rw [← hpow] at hlt
      exact (lt_of_pow_lt_pow_left₀ p hτ.le hlt).le
    refine ⟨h, hh0, hle, ?_, ?_⟩
    · rw [hpow, hr]
      field_simp
      exact le_rfl
    · set α : ℝ := (j : ℝ) / p with hα
      have e1 : h ^ j = r ^ α := by
        rw [hh, ← Real.rpow_natCast, ← Real.rpow_mul hr0.le]
        congr 1
        rw [hα]
        field_simp
      have e2 : M₀ / h ^ j = M₀ ^ (1 - α) * Mp ^ α := by
        rw [e1, hr, Real.div_rpow hM.le hMp0.le, Real.rpow_sub hM, Real.rpow_one]
        have : 0 < M₀ ^ α := by positivity
        have : 0 < Mp ^ α := by positivity
        field_simp
      rw [e2]
      have : 0 ≤ M₀ / τ₀ ^ j := by positivity
      linarith
end LandauKolmogorov
open LandauKolmogorov in
theorem landauKolmogorovAtZero_holds : LandauKolmogorovAtZero := by
  intro p j hj
  have hp : 0 < p := by omega
  obtain ⟨K, hK, hco⟩ := exists_coeff_le_of_values_at_nodes p hp
  refine ⟨2 * (K + 1) * j.factorial, by positivity, ?_⟩
  intro g τ₀ M₀ Mp hτ hM hMp hd h0 hpb
  obtain ⟨h, hh0, hle, hMh, hfin⟩ := exists_step_size p j hj τ₀ M₀ Mp hτ hM hMp
  set a : Fin p → ℝ := fun i => g i 0 * h ^ (i : ℕ) / (i : ℕ).factorial with ha
  have hvals : ∀ l : Fin p, |∑ i : Fin p, a i * ((l : ℝ) / p) ^ (i : ℕ)| ≤ 2 * M₀ := by
    intro l
    set s : ℝ := h * ((l : ℝ) / p) with hs
    have hpR : (0 : ℝ) < p := by exact_mod_cast hp
    have hl1 : (l : ℝ) / p ≤ 1 := by
      rw [div_le_one hpR]
      exact_mod_cast l.2.le
    have hl0 : 0 ≤ (l : ℝ) / p := by positivity
    have hs0 : 0 ≤ s := by positivity
    have hsh : s ≤ h := by
      simp only [hs]
      nlinarith
    have hsτ : |s| ≤ τ₀ := by
      rw [abs_of_nonneg hs0]
      linarith
    have ht := taylor_remainder_le_of_hasDerivAt_chain τ₀ Mp hMp p g hd hpb s hsτ
    have e : ∑ i : Fin p, a i * ((l : ℝ) / p) ^ (i : ℕ) =
        ∑ i ∈ Finset.range p, g i 0 * s ^ i / i.factorial := by
      rw [← Fin.sum_univ_eq_sum_range (fun i => g i 0 * s ^ i / i.factorial)]
      apply Finset.sum_congr rfl
      intro i _
      simp only [ha, hs, mul_pow]
      ring
    rw [e]
    have h1 := h0 s hsτ
    have h2 : Mp * |s| ^ p ≤ M₀ := by
      rw [abs_of_nonneg hs0]
      calc Mp * s ^ p ≤ Mp * h ^ p := by gcongr
        _ ≤ M₀ := hMh
    have h3 := abs_sub_abs_le_abs_sub (∑ i ∈ Finset.range p, g i 0 * s ^ i / i.factorial) (g 0 s)
    rw [abs_sub_comm] at h3
    linarith
  have hj' := hco a (2 * M₀) hvals ⟨j, hj⟩
  simp only [ha] at hj'
  have hf : (0 : ℝ) < j.factorial := by exact_mod_cast Nat.factorial_pos j
  have hhj : 0 < h ^ j := by positivity
  rw [abs_div, abs_mul, abs_of_pos hhj, abs_of_pos hf, div_le_iff₀ hf] at hj'
  have h5 : |g j 0| ≤ K * (2 * M₀) * j.factorial / h ^ j := by
    rw [le_div_iff₀ hhj]
    exact hj'
  have h6 : K * (2 * M₀) * j.factorial / h ^ j = 2 * K * j.factorial * (M₀ / h ^ j) := by ring
  rw [h6] at h5
  have h7 : 0 ≤ M₀ / h ^ j := by positivity
  calc |g j 0| ≤ 2 * K * j.factorial * (M₀ / h ^ j) := h5
    _ ≤ 2 * (K + 1) * j.factorial * (M₀ / h ^ j) := by
        apply mul_le_mul_of_nonneg_right _ h7
        nlinarith
    _ ≤ 2 * (K + 1) * j.factorial * _ := by
        apply mul_le_mul_of_nonneg_left hfin
        positivity
end YangMills.Construction.ColdStepAtMirrorFrames
end
