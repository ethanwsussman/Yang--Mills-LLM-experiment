import YangMills.Construction.ClusterExpansionOfAStep.JetsOfTheExponential
import Mathlib
set_option autoImplicit false
noncomputable section
open scoped Quaternion
namespace YangMills.Construction.QuaternionExponential
open BlockAverages
def expImaginary : imaginaryQuaternions → ℍ[ℝ] := fun w => NormedSpace.exp (w : ℍ[ℝ])
theorem contDiff_expImaginary : ContDiff ℝ ⊤ expImaginary := by
  have h : AnalyticOnNhd ℝ (NormedSpace.exp : ℍ[ℝ] → ℍ[ℝ]) Set.univ := fun x _ => NormedSpace.exp_analytic x
  exact h.contDiff.comp imaginaryQuaternions.subtypeL.contDiff
theorem norm_expImaginary (v : imaginaryQuaternions) : ‖expImaginary v‖ = 1 := by
  have hu : expImaginary v ∈ unitary ℍ[ℝ] := exp_imaginary_mem_unitary v
  have h1 := (Unitary.mem_iff.mp hu).1
  have h2 : ‖star (expImaginary v) * expImaginary v‖ = 1 := by rw [h1]; simp
  rw [norm_mul, norm_star] at h2
  nlinarith [norm_nonneg (expImaginary v)]
def halveImaginary : imaginaryQuaternions →L[ℝ] imaginaryQuaternions :=
  (1 / 2 : ℝ) • ContinuousLinearMap.id ℝ imaginaryQuaternions
theorem expImaginary_eq_sq_halve (v : imaginaryQuaternions) :
    expImaginary v = (expImaginary ∘ halveImaginary) v * (expImaginary ∘ halveImaginary) v := by
  have h : ((halveImaginary v : imaginaryQuaternions) : ℍ[ℝ]) + ((halveImaginary v : imaginaryQuaternions) : ℍ[ℝ]) =
      (v : ℍ[ℝ]) := by
    simp only [halveImaginary, _root_.smul_apply, ContinuousLinearMap.id_apply, Submodule.coe_smul]
    rw [← add_smul]
    norm_num
  simp only [Function.comp, expImaginary]
  have hr : (NormedSpace.expSeries ℝ ℍ[ℝ]).radius = ⊤ := NormedSpace.expSeries_radius_eq_top ℝ ℍ[ℝ]
  rw [← NormedSpace.exp_add_of_commute_of_mem_ball (𝕂 := ℝ) (Commute.refl _) (by rw [hr]; simp) (by rw [hr]; simp), h]
theorem norm_halveImaginary_le : ‖halveImaginary‖ ≤ 1 / 2 := by
  refine ContinuousLinearMap.opNorm_le_bound _ (by norm_num) fun v => ?_
  simp [halveImaginary, norm_smul]
theorem norm_iteratedFDeriv_comp_halve_le (i : ℕ) (v : imaginaryQuaternions) :
    ‖iteratedFDeriv ℝ i (expImaginary ∘ halveImaginary) v‖ ≤
      (1 / 2) ^ i * ‖iteratedFDeriv ℝ i expImaginary (halveImaginary v)‖ := by
  have h := halveImaginary.iteratedFDeriv_comp_right contDiff_expImaginary v (i := i) (by exact_mod_cast le_top)
  rw [h]
  refine (ContinuousMultilinearMap.norm_compContinuousLinearMap_le _ _).trans ?_
  rw [Finset.prod_const, Finset.card_univ, Fintype.card_fin, mul_comm]
  exact mul_le_mul_of_nonneg_right (pow_le_pow_left₀ (norm_nonneg _) norm_halveImaginary_le i) (norm_nonneg _)
theorem iteratedDerivBounded_holds : IteratedDerivBounded := by
  intro j
  change ∃ C : ℝ, 0 ≤ C ∧ ∀ v : imaginaryQuaternions, ‖iteratedFDeriv ℝ j expImaginary v‖ ≤ C
  induction j using Nat.strong_induction_on with
  | _ j ih =>
    rcases j with _ | J
    · exact ⟨1, zero_le_one, fun v => by rw [norm_iteratedFDeriv_zero, norm_expImaginary]⟩
    · choose! C hC0 hC using ih
      obtain ⟨M, hM⟩ := (isCompact_closedBall (0 : imaginaryQuaternions) 1).exists_bound_of_continuousOn
        (f := iteratedFDeriv ℝ (J + 1) expImaginary)
        (contDiff_expImaginary.continuous_iteratedFDeriv (by exact_mod_cast le_top)).continuousOn
      set c : ℝ := ∑ i ∈ Finset.range J, ((J + 1).choose (i + 1) : ℝ) * (C (i + 1) * C (J + 1 - (i + 1))) with hc
      have hc0 : 0 ≤ c := Finset.sum_nonneg fun i hi => by
        have h1 := hC0 (i + 1) (by have := Finset.mem_range.mp hi; omega)
        have h2 := hC0 (J + 1 - (i + 1)) (by omega)
        positivity
      set B : ℝ := max (max M 0) (2 * c) with hB
      have hB0 : 0 ≤ B := le_max_of_le_left (le_max_right _ _)
      have hBM : M ≤ B := le_max_of_le_left (le_max_left _ _)
      have hBc : 2 * c ≤ B := le_max_right _ _
      have hstep : ∀ m : ℕ, ∀ v : imaginaryQuaternions, ‖v‖ ≤ 2 ^ m →
          ‖iteratedFDeriv ℝ (J + 1) expImaginary v‖ ≤ B := by
        intro m
        induction m with
        | zero =>
          intro v hv
          exact (hM v (by simpa using hv)).trans hBM
        | succ m ihm =>
          intro v hv
          have hsq : expImaginary = fun w => (expImaginary ∘ halveImaginary) w * (expImaginary ∘ halveImaginary) w :=
            funext expImaginary_eq_sq_halve
          have hcd : ContDiff ℝ ⊤ (expImaginary ∘ halveImaginary) :=
            contDiff_expImaginary.comp halveImaginary.contDiff
          have hmul := norm_iteratedFDeriv_mul_le (n := J + 1) hcd hcd v (by exact_mod_cast le_top)
          rw [← hsq] at hmul
          have hu : ‖halveImaginary v‖ ≤ 2 ^ m := by
            have h1 := ContinuousLinearMap.le_opNorm halveImaginary v
            have h2 := norm_halveImaginary_le
            have h3 : ‖halveImaginary‖ * ‖v‖ ≤ 1 / 2 * ‖v‖ := mul_le_mul_of_nonneg_right h2 (norm_nonneg _)
            rw [pow_succ] at hv
            linarith
          have hzero : ∀ w : imaginaryQuaternions, ‖iteratedFDeriv ℝ 0 (expImaginary ∘ halveImaginary) w‖ = 1 :=
            fun w => by
              rw [norm_iteratedFDeriv_zero]
              exact norm_expImaginary _
          have hlast : ‖iteratedFDeriv ℝ (J + 1) (expImaginary ∘ halveImaginary) v‖ ≤ (1 / 2) ^ (J + 1) * B :=
            (norm_iteratedFDeriv_comp_halve_le _ v).trans (mul_le_mul_of_nonneg_left (ihm _ hu) (by positivity))
          have hmid : ∀ i ∈ Finset.range J,
              ((J + 1).choose (i + 1) : ℝ) * ‖iteratedFDeriv ℝ (i + 1) (expImaginary ∘ halveImaginary) v‖ *
                ‖iteratedFDeriv ℝ (J + 1 - (i + 1)) (expImaginary ∘ halveImaginary) v‖ ≤
              ((J + 1).choose (i + 1) : ℝ) * (C (i + 1) * C (J + 1 - (i + 1))) := by
            intro i hi
            have hiJ := Finset.mem_range.mp hi
            have e1 : ‖iteratedFDeriv ℝ (i + 1) (expImaginary ∘ halveImaginary) v‖ ≤ C (i + 1) := by
              refine (norm_iteratedFDeriv_comp_halve_le _ v).trans ?_
              refine (mul_le_of_le_one_left (norm_nonneg _) (pow_le_one₀ (by norm_num) (by norm_num))).trans ?_
              exact hC _ (by omega) _
            have e2 : ‖iteratedFDeriv ℝ (J + 1 - (i + 1)) (expImaginary ∘ halveImaginary) v‖ ≤
                C (J + 1 - (i + 1)) := by
              refine (norm_iteratedFDeriv_comp_halve_le _ v).trans ?_
              refine (mul_le_of_le_one_left (norm_nonneg _) (pow_le_one₀ (by norm_num) (by norm_num))).trans ?_
              exact hC _ (by omega) _
            rw [mul_assoc]
            exact mul_le_mul_of_nonneg_left (mul_le_mul e1 e2 (norm_nonneg _) (hC0 _ (by omega))) (Nat.cast_nonneg _)
          refine hmul.trans ?_
          rw [Finset.sum_range_succ, Finset.sum_range_succ']
          have hsum := Finset.sum_le_sum hmid
          rw [← hc] at hsum
          have h00 : ‖iteratedFDeriv ℝ (J + 1 - (J + 1)) (expImaginary ∘ halveImaginary) v‖ = 1 := by
            rw [Nat.sub_self]
            exact hzero v
          rw [h00]
          simp only [Nat.choose_zero_right, Nat.choose_self, Nat.cast_one, one_mul, mul_one, Nat.sub_zero, hzero]
          rcases J with _ | J'
          · simp only [Finset.range_zero, Finset.sum_empty, zero_add] at hc hsum ⊢
            norm_num at hlast ⊢
            linarith
          · have hq : ((1 : ℝ) / 2) ^ (J' + 1 + 1) ≤ 1 / 4 := by
              rw [pow_succ, pow_succ]
              have : ((1 : ℝ) / 2) ^ J' ≤ 1 := pow_le_one₀ (by norm_num) (by norm_num)
              nlinarith
            have hl2 : ‖iteratedFDeriv ℝ (J' + 1 + 1) (expImaginary ∘ halveImaginary) v‖ ≤ 1 / 4 * B :=
              hlast.trans (mul_le_mul_of_nonneg_right hq hB0)
            linarith
      refine ⟨B, hB0, fun v => ?_⟩
      obtain ⟨m, hm⟩ := pow_unbounded_of_one_lt ‖v‖ (one_lt_two : (1 : ℝ) < 2)
      exact hstep m v hm.le
end YangMills.Construction.QuaternionExponential
end
