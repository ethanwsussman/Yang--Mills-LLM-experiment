import YangMills.Construction.Matrices.ElementaryMatrixInequalities
import YangMills.Construction.Matrices.LinearMapsCompositesAndCoordinatesOfRealAnalyticMapsProof
import YangMills.Construction.Matrices.NormExpLogConjugation
import YangMills.Construction.Matrices.SpecialUnitaryAngles
import Mathlib
open scoped Matrix.Norms.L2Operator Topology NNReal
open Metric Filter
noncomputable section
namespace YangMills.Construction.Matrices.ComplexMatrix2.ElementaryBounds
section OneVariable
variable {E F : Type} [NormedAddCommGroup E] [NormedSpace ℂ E]
  [NormedAddCommGroup F] [NormedSpace ℂ F]
theorem hasDerivAt_comp_affineLine {f : E → F} {b v : E} (hf : DifferentiableAt ℂ f b) :
    HasDerivAt (fun t : ℂ => f (b + t • v)) (fderiv ℂ f b v) 0 := by
  have hline : HasDerivAt (fun t : ℂ => b + t • v) v 0 := by
    simpa using ((hasDerivAt_id (0 : ℂ)).smul_const v).const_add b
  have hfd : HasFDerivAt f (fderiv ℂ f b) (b + (0 : ℂ) • v) := by
    simpa using hf.hasFDerivAt
  exact hfd.comp_hasDerivAt (0 : ℂ) hline
theorem norm_cauchyPowerSeries_le_of_norm_le {h : ℂ → F} {ρ : ℝ≥0} {R M : ℝ} (hρ : 0 < (ρ : ℝ))
    (hρR : (ρ : ℝ) < R) (hM : ∀ t ∈ ball (0 : ℂ) R, ‖h t‖ ≤ M) (n : ℕ) :
    ‖cauchyPowerSeries h 0 (ρ : ℝ) n‖ ≤ M * (ρ : ℝ)⁻¹ ^ n := by
  refine (norm_cauchyPowerSeries_le h 0 (ρ : ℝ) n).trans ?_
  have hcircle : ∀ θ : ℝ, ‖h (circleMap 0 (ρ : ℝ) θ)‖ ≤ M := by
    intro θ
    apply hM
    rw [mem_ball_zero_iff, norm_circleMap_zero, abs_of_pos hρ]
    exact hρR
  have hint : ∫ θ in (0 : ℝ)..2 * Real.pi, ‖h (circleMap 0 (ρ : ℝ) θ)‖ ≤ M * (2 * Real.pi) := by
    have h₁ := intervalIntegral.norm_integral_le_of_norm_le_const (a := (0 : ℝ))
      (b := 2 * Real.pi) (f := fun θ => ‖h (circleMap 0 (ρ : ℝ) θ)‖) (C := M)
      (fun θ _ => by simpa using hcircle θ)
    have h₂ : |2 * Real.pi - 0| = 2 * Real.pi := by
      rw [sub_zero, abs_of_pos Real.two_pi_pos]
    rw [h₂] at h₁
    exact (le_abs_self _).trans h₁
  have hpi : 0 < 2 * Real.pi := Real.two_pi_pos
  have havg : (2 * Real.pi)⁻¹ * ∫ θ in (0 : ℝ)..2 * Real.pi, ‖h (circleMap 0 (ρ : ℝ) θ)‖ ≤ M := by
    calc (2 * Real.pi)⁻¹ * ∫ θ in (0 : ℝ)..2 * Real.pi, ‖h (circleMap 0 (ρ : ℝ) θ)‖
        ≤ (2 * Real.pi)⁻¹ * (M * (2 * Real.pi)) :=
          mul_le_mul_of_nonneg_left hint (inv_nonneg.mpr hpi.le)
      _ = M := by field_simp
  rw [abs_of_pos hρ]
  exact mul_le_mul_of_nonneg_right havg (pow_nonneg (inv_nonneg.mpr hρ.le) n)
theorem norm_taylorRemainder_two_le_of_lt [CompleteSpace F] {h : ℂ → F} {ρ R M : ℝ} {t : ℂ}
    (hρ : 0 < ρ) (hρR : ρ < R)
    (ht : ‖t‖ < ρ) (hd : DifferentiableOn ℂ h (ball 0 R)) (hM : ∀ t ∈ ball (0 : ℂ) R, ‖h t‖ ≤ M) :
    ‖h t - h 0 - t • deriv h 0‖ ≤ M * ‖t‖ ^ 2 / (ρ * (ρ - ‖t‖)) := by
  lift ρ to ℝ≥0 using hρ.le
  have hd' : DifferentiableOn ℂ h (closedBall 0 (ρ : ℝ)) :=
    hd.mono (closedBall_subset_ball hρR)
  have hp := hd'.hasFPowerSeriesOnBall (by exact_mod_cast hρ)
  set p := cauchyPowerSeries h 0 (ρ : ℝ) with hpdef
  have hsum : HasSum (fun n => p n fun _ => t) (h t) := by
    have := hp.hasSum (y := t) (by
      rw [Metric.eball_coe, mem_ball_zero_iff]
      exact ht)
    simpa using this
  have hsum2 := (hasSum_nat_add_iff' 2).mpr hsum
  have h0 : (p 0 fun _ => t) = h 0 := hp.coeff_zero _
  have h1 : (p 1 fun _ => t) = t • deriv h 0 := by
    rw [hp.hasFPowerSeriesAt.deriv, FormalMultilinearSeries.apply_eq_pow_smul_coeff, pow_one]
    rfl
  simp only [Finset.sum_range_succ, Finset.sum_range_zero, zero_add, h0, h1] at hsum2
  have hq : ‖t‖ / ρ < 1 := (div_lt_one hρ).mpr ht
  have hq0 : 0 ≤ ‖t‖ / ρ := div_nonneg (norm_nonneg _) hρ.le
  have hgeo : HasSum (fun n : ℕ => M * (‖t‖ / ρ) ^ 2 * (‖t‖ / ρ) ^ n)
      (M * (‖t‖ / ρ) ^ 2 * (1 - ‖t‖ / ρ)⁻¹) :=
    (hasSum_geometric_of_lt_one hq0 hq).mul_left _
  have hle := hsum2.norm_le_of_bounded hgeo (fun n => by
    calc ‖p (n + 2) fun _ => t‖ ≤ ‖p (n + 2)‖ * ∏ _i : Fin (n + 2), ‖t‖ :=
          ContinuousMultilinearMap.le_opNorm _ _
      _ ≤ (M * (ρ : ℝ)⁻¹ ^ (n + 2)) * ∏ _i : Fin (n + 2), ‖t‖ :=
          mul_le_mul_of_nonneg_right (norm_cauchyPowerSeries_le_of_norm_le hρ hρR hM _)
            (Finset.prod_nonneg fun _ _ => norm_nonneg _)
      _ = M * (‖t‖ / ρ) ^ 2 * (‖t‖ / ρ) ^ n := by
          rw [Finset.prod_const, Finset.card_univ, Fintype.card_fin, div_eq_mul_inv, mul_pow,
            mul_pow]
          ring)
  have hfin : M * (‖t‖ / ρ) ^ 2 * (1 - ‖t‖ / ρ)⁻¹ = M * ‖t‖ ^ 2 / (ρ * (ρ - ‖t‖)) := by
    have h₁ : (ρ : ℝ) - ‖t‖ ≠ 0 := (sub_pos.mpr ht).ne'
    have h₂ : (1 : ℝ) - ‖t‖ / ρ = (ρ - ‖t‖) / ρ := by field_simp
    rw [h₂]
    field_simp
  rw [← hfin, sub_sub]
  exact hle
theorem norm_taylorRemainder_two_le [CompleteSpace F] {h : ℂ → F} {R M : ℝ} {t : ℂ}
    (ht : ‖t‖ < R) (hd : DifferentiableOn ℂ h (ball 0 R)) (hM : ∀ t ∈ ball (0 : ℂ) R, ‖h t‖ ≤ M) :
    ‖h t - h 0 - t • deriv h 0‖ ≤ M * ‖t‖ ^ 2 / (R * (R - ‖t‖)) := by
  have hR : 0 < R := (norm_nonneg _).trans_lt ht
  have hden : R * (R - ‖t‖) ≠ 0 := (mul_pos hR (sub_pos.mpr ht)).ne'
  have hlim : Tendsto (fun ρ : ℝ => M * ‖t‖ ^ 2 / (ρ * (ρ - ‖t‖))) (𝓝[<] R)
      (𝓝 (M * ‖t‖ ^ 2 / (R * (R - ‖t‖)))) := by
    have hc : ContinuousAt (fun ρ : ℝ => M * ‖t‖ ^ 2 / (ρ * (ρ - ‖t‖))) R :=
      continuousAt_const.div (continuousAt_id.mul (continuousAt_id.sub continuousAt_const)) hden
    exact hc.tendsto.mono_left nhdsWithin_le_nhds
  refine ge_of_tendsto hlim ?_
  filter_upwards [Ioo_mem_nhdsLT ht] with ρ hρ
  exact norm_taylorRemainder_two_le_of_lt ((norm_nonneg _).trans_lt hρ.1) hρ.2 hρ.1 hd hM
theorem norm_deriv_zero_le {h : ℂ → F} {R M : ℝ} (hR : 0 < R) (hd : DifferentiableOn ℂ h (ball 0 R))
    (hM : ∀ t ∈ ball (0 : ℂ) R, ‖h t‖ ≤ M) : ‖deriv h 0‖ ≤ M / R := by
  have hlim : Tendsto (fun ρ : ℝ => M / ρ) (𝓝[<] R) (𝓝 (M / R)) := by
    have hc : ContinuousAt (fun ρ : ℝ => M / ρ) R :=
      continuousAt_const.div continuousAt_id hR.ne'
    exact hc.tendsto.mono_left nhdsWithin_le_nhds
  refine ge_of_tendsto hlim ?_
  filter_upwards [Ioo_mem_nhdsLT hR] with ρ hρ
  have hdc : DiffContOnCl ℂ h (ball 0 ρ) :=
    (hd.mono (closedBall_subset_ball hρ.2)).diffContOnCl_ball subset_rfl
  refine Complex.norm_deriv_le_of_forall_mem_sphere_norm_le hρ.1 hdc fun z hz => hM z ?_
  rw [mem_ball_zero_iff]
  rw [mem_sphere_zero_iff_norm] at hz
  rw [hz]
  exact hρ.2
end OneVariable
section Ball
variable {E F : Type} [NormedAddCommGroup E] [NormedSpace ℂ E]
  [NormedAddCommGroup F] [NormedSpace ℂ F]
theorem cauchy_schwarz_estimates_ball [CompleteSpace F] {r M : ℝ} {f : E → F}
    (hf : DifferentiableOn ℂ f (ball 0 r)) (hM : ∀ a ∈ ball (0 : E) r, ‖f a‖ ≤ M)
    {a : E} (ha : a ∈ ball (0 : E) r) :
    (∀ δ : E, ‖fderiv ℂ f a δ‖ ≤ M * ‖δ‖ / (r - ‖a‖)) ∧
      ‖f a - f 0 - fderiv ℂ f 0 a‖ ≤ M * ‖a‖ ^ 2 / (r * (r - ‖a‖)) ∧
      (f 0 = 0 → ‖f a‖ ≤ M * ‖a‖ / r) := by
  have har : ‖a‖ < r := mem_ball_zero_iff.mp ha
  have hr : 0 < r := (norm_nonneg _).trans_lt har
  have hgap : 0 < r - ‖a‖ := sub_pos.mpr har
  have hopen : IsOpen (ball (0 : E) r) := isOpen_ball
  have h0 : (0 : E) ∈ ball (0 : E) r := mem_ball_self hr
  refine ⟨?_, ?_, ?_⟩
  · intro δ
    rcases eq_or_ne δ 0 with rfl | hδ
    · simp
    have hδ' : 0 < ‖δ‖ := norm_pos_iff.mpr hδ
    set R := (r - ‖a‖) / ‖δ‖ with hRdef
    have hR : 0 < R := div_pos hgap hδ'
    have hin : ∀ t ∈ ball (0 : ℂ) R, a + t • δ ∈ ball (0 : E) r := by
      intro t ht
      rw [mem_ball_zero_iff] at ht ⊢
      have h₁ : ‖t‖ * ‖δ‖ < r - ‖a‖ := (lt_div_iff₀ hδ').mp ht
      calc ‖a + t • δ‖ ≤ ‖a‖ + ‖t‖ * ‖δ‖ := by
            simpa [norm_smul] using norm_add_le a (t • δ)
        _ < r := by linarith
    have hline : DifferentiableOn ℂ (fun t : ℂ => f (a + t • δ)) (ball 0 R) := by
      intro t ht
      have hat := (hf.differentiableAt (hopen.mem_nhds (hin t ht)))
      have hl : DifferentiableAt ℂ (fun t : ℂ => a + t • δ) t := by fun_prop
      exact (hat.comp t hl).differentiableWithinAt
    have hder : deriv (fun t : ℂ => f (a + t • δ)) 0 = fderiv ℂ f a δ :=
      (hasDerivAt_comp_affineLine (hf.differentiableAt (hopen.mem_nhds ha))).deriv
    have hb := norm_deriv_zero_le hR hline (fun t ht => hM _ (hin t ht))
    rw [hder] at hb
    calc ‖fderiv ℂ f a δ‖ ≤ M / R := hb
      _ = M * ‖δ‖ / (r - ‖a‖) := by
        rw [hRdef]
        field_simp
  · rcases eq_or_ne a 0 with rfl | ha0
    · simp
    have ha' : 0 < ‖a‖ := norm_pos_iff.mpr ha0
    set u : E := ((‖a‖ : ℂ)⁻¹) • a with hu
    have hunorm : ‖u‖ = 1 := by
      rw [hu, norm_smul, norm_inv, Complex.norm_real, norm_norm]
      exact inv_mul_cancel₀ ha'.ne'
    have hau : ((‖a‖ : ℝ) : ℂ) • u = a := by
      rw [hu, smul_smul, mul_inv_cancel₀ (by exact_mod_cast ha'.ne'), one_smul]
    have hin : ∀ t ∈ ball (0 : ℂ) r, (0 : E) + t • u ∈ ball (0 : E) r := by
      intro t ht
      rw [mem_ball_zero_iff] at ht ⊢
      simpa [norm_smul, hunorm] using ht
    have hline : DifferentiableOn ℂ (fun t : ℂ => f ((0 : E) + t • u)) (ball 0 r) := by
      intro t ht
      have hat := (hf.differentiableAt (hopen.mem_nhds (hin t ht)))
      have hl : DifferentiableAt ℂ (fun t : ℂ => (0 : E) + t • u) t := by fun_prop
      exact (hat.comp t hl).differentiableWithinAt
    have hder : deriv (fun t : ℂ => f ((0 : E) + t • u)) 0 = fderiv ℂ f 0 u :=
      (hasDerivAt_comp_affineLine (hf.differentiableAt (hopen.mem_nhds h0))).deriv
    have hnorm : ‖((‖a‖ : ℝ) : ℂ)‖ = ‖a‖ := by
      rw [Complex.norm_real, norm_norm]
    have hb := norm_taylorRemainder_two_le (t := ((‖a‖ : ℝ) : ℂ)) (by rw [hnorm]; exact har) hline
      (fun t ht => hM _ (hin t ht))
    rw [hder, hnorm] at hb
    simp only [zero_add, zero_smul, hau] at hb
    rwa [← map_smul, hau] at hb
  · intro hf0
    have hmaps : Set.MapsTo f (ball 0 r) (closedBall (f 0) M) := by
      intro x hx
      rw [hf0, mem_closedBall_zero_iff]
      exact hM x hx
    have hb := Complex.dist_le_div_mul_dist_of_mapsTo_ball hf hmaps ha
    rw [hf0, dist_zero_right, dist_zero_right] at hb
    calc ‖f a‖ ≤ M / r * ‖a‖ := hb
      _ = M * ‖a‖ / r := by ring
end Ball
section Products
theorem norm_matExp_sub_one_sub_le (X : ComplexMatrix2) :
    operatorNorm (matExp X - 1 - X) ≤ Real.exp (operatorNorm X) - 1 - operatorNorm X := by
  have h₁ := (hasSum_nat_add_iff' 2).mpr (NormedSpace.exp_series_hasSum_exp' (𝕂 := ℂ) X)
  have h₂ := (hasSum_nat_add_iff' 2).mpr (NormedSpace.expSeries_div_hasSum_exp (operatorNorm X))
  simp only [Finset.sum_range_succ, Finset.sum_range_zero, zero_add, pow_zero, pow_one,
    Nat.factorial_zero, Nat.factorial_one, Nat.cast_one, inv_one, one_smul, div_one,
    ← Real.exp_eq_exp_ℝ] at h₁ h₂
  have hle := h₁.norm_le_of_bounded h₂ (fun n => by
    rw [norm_smul, norm_inv, Complex.norm_natCast, div_eq_inv_mul]
    exact mul_le_mul_of_nonneg_left (norm_pow_le' X (Nat.succ_pos _)) (by positivity))
  simpa [sub_sub] using hle
theorem norm_expListProduct_sub_le (hexp : ∀ Z : ComplexMatrix2,
    operatorNorm (matExp Z) ≤ Real.exp (operatorNorm Z) ∧
      operatorNorm (matExp Z - 1) ≤ Real.exp (operatorNorm Z) - 1) :
    ∀ (n : ℕ) (X : Fin n → ComplexMatrix2), operatorNorm (expListProduct X - 1 - ∑ j, X j) ≤
      Real.exp (∑ j, operatorNorm (X j)) - 1 - ∑ j, operatorNorm (X j) := by
  intro n
  induction n with
  | zero =>
    intro X
    simp [expListProduct]
  | succ n ih =>
    intro X
    have hprod : expListProduct X = matExp (X 0) * expListProduct fun i => X i.succ := by
      simp [expListProduct, List.ofFn_succ]
    rw [hprod, Fin.sum_univ_succ, Fin.sum_univ_succ]
    set P := expListProduct fun i => X i.succ
    set S := ∑ i : Fin n, X i.succ with hS
    set s := ∑ i : Fin n, operatorNorm (X i.succ) with hs
    set a := operatorNorm (X 0) with ha
    have hSs : operatorNorm S ≤ s := norm_sum_le _ _
    have hid : matExp (X 0) * P - 1 - (X 0 + S) =
        matExp (X 0) * (P - 1 - S) + (matExp (X 0) - 1 - X 0) + (matExp (X 0) - 1) * S := by
      noncomm_ring
    have hQ : operatorNorm (P - 1 - S) ≤ Real.exp s - 1 - s := ih _
    have hQ0 : 0 ≤ operatorNorm (P - 1 - S) := norm_nonneg _
    have he := (hexp (X 0)).1
    have he1 := (hexp (X 0)).2
    have hR := norm_matExp_sub_one_sub_le (X 0)
    have hea : 0 ≤ Real.exp a := (Real.exp_pos a).le
    have hea1 : 0 ≤ Real.exp a - 1 := (norm_nonneg _).trans he1
    have h₁ : operatorNorm (matExp (X 0) * (P - 1 - S)) ≤ Real.exp a * (Real.exp s - 1 - s) :=
      (norm_mul_le _ _).trans (mul_le_mul he hQ hQ0 hea)
    have h₂ : operatorNorm ((matExp (X 0) - 1) * S) ≤ (Real.exp a - 1) * s :=
      (norm_mul_le _ _).trans (mul_le_mul he1 hSs (norm_nonneg _) hea1)
    have h₃ : operatorNorm (matExp (X 0) * (P - 1 - S) + (matExp (X 0) - 1 - X 0) +
          (matExp (X 0) - 1) * S) ≤
        operatorNorm (matExp (X 0) * (P - 1 - S)) + operatorNorm (matExp (X 0) - 1 - X 0) +
          operatorNorm ((matExp (X 0) - 1) * S) :=
      (norm_add_le _ _).trans (add_le_add_left (norm_add_le _ _) _)
    rw [hid, Real.exp_add]
    nlinarith [h₁, h₂, h₃, hR]
theorem real_exp_sub_one_sub_le_sq {s : ℝ} (h₀ : 0 ≤ s) (h₁ : s ≤ 1) :
    Real.exp s - 1 - s ≤ s ^ 2 :=
  (le_abs_self _).trans (Real.abs_exp_sub_one_sub_id_le (by rwa [abs_of_nonneg h₀]))
theorem expListProduct_estimates (hE : ExpLogEstimates) (n : ℕ) (X : Fin n → ComplexMatrix2) :
    (∑ j, operatorNorm (X j) ≤ 1 →
      operatorNorm (expListProduct X - 1 - ∑ j, X j) ≤ (∑ j, operatorNorm (X j)) ^ 2 ∧
      operatorNorm (expListProduct X - matExp (∑ j, X j)) ≤ 2 * (∑ j, operatorNorm (X j)) ^ 2) ∧
    (∑ j, operatorNorm (X j) ≤ 1 / 4 →
      operatorNorm (logSeries (expListProduct X) - ∑ j, X j) ≤
        4 * (∑ j, operatorNorm (X j)) ^ 2) := by
  obtain ⟨e₁, -, -, -, e₅, -, -, -, e₉, -⟩ := hE
  have key := norm_expListProduct_sub_le e₁ n X
  set P := expListProduct X
  set S := ∑ j, X j with hS
  set s := ∑ j, operatorNorm (X j) with hs
  have hs0 : 0 ≤ s := Finset.sum_nonneg fun _ _ => norm_nonneg _
  have hSs : operatorNorm S ≤ s := norm_sum_le _ _
  have hS0 : 0 ≤ operatorNorm S := norm_nonneg _
  have hsmall : s ≤ 1 →
      operatorNorm (P - 1 - S) ≤ s ^ 2 ∧ operatorNorm (matExp S - 1 - S) ≤ s ^ 2 := by
    intro h1
    refine ⟨key.trans (real_exp_sub_one_sub_le_sq hs0 h1), ?_⟩
    refine (norm_matExp_sub_one_sub_le S).trans
      ((real_exp_sub_one_sub_le_sq hS0 (hSs.trans h1)).trans ?_)
    exact pow_le_pow_left₀ hS0 hSs 2
  have hdiff : s ≤ 1 → operatorNorm (P - matExp S) ≤ 2 * s ^ 2 := by
    intro h1
    obtain ⟨h₁, h₂⟩ := hsmall h1
    have hid : P - matExp S = (P - 1 - S) - (matExp S - 1 - S) := by abel
    rw [hid]
    have := norm_sub_le (P - 1 - S) (matExp S - 1 - S)
    linarith
  refine ⟨fun h1 => ⟨(hsmall h1).1, hdiff h1⟩, fun h4 => ?_⟩
  have h1 : s ≤ 1 := by linarith
  obtain ⟨h₁, h₂⟩ := hsmall h1
  have hsq : s ^ 2 ≤ 1 / 16 := by nlinarith
  have hA : operatorNorm (P - 1) ≤ 1 / 2 := by
    have hid : P - 1 = (P - 1 - S) + S := by abel
    rw [hid]
    have := norm_add_le (P - 1 - S) S
    linarith
  have hB : operatorNorm (matExp S - 1) ≤ 1 / 2 := by
    have hid : matExp S - 1 = (matExp S - 1 - S) + S := by abel
    rw [hid]
    have := norm_add_le (matExp S - 1 - S) S
    linarith
  have hlog2 : operatorNorm S < Real.log 2 := by
    have := Real.log_two_gt_d9
    linarith
  have hlogS : logSeries (matExp S) = S := (e₅ S hlog2).2
  have hlip := (e₉ (1 / 2) P (matExp S) (by norm_num) (by norm_num) hA hB).2.2.2
  rw [hlogS] at hlip
  have := hdiff h1
  have h2 : (1 : ℝ) / (1 - 1 / 2) = 2 := by norm_num
  rw [h2] at hlip
  linarith
theorem matExp_mul_matExp_estimates (hE : ExpLogEstimates) {A B : ComplexMatrix2}
    (h : operatorNorm A + operatorNorm B ≤ 1 / 4) :
    operatorNorm (matExp A * matExp B - 1) < 1 ∧
      operatorNorm (logSeries (matExp A * matExp B) - (A + B)) ≤
        4 * (operatorNorm A + operatorNorm B) ^ 2 := by
  have hp := expListProduct_estimates hE 2 ![A, B]
  have hprod : expListProduct ![A, B] = matExp A * matExp B := by
    simp [expListProduct, List.ofFn_succ]
  simp only [Fin.sum_univ_two, Matrix.cons_val_zero, Matrix.cons_val_one, hprod] at hp
  have h₁ := (hp.1 (by linarith)).1
  refine ⟨?_, hp.2 h⟩
  have hid : matExp A * matExp B - 1 = (matExp A * matExp B - 1 - (A + B)) + (A + B) := by abel
  rw [hid]
  have h₂ := norm_add_le (matExp A * matExp B - 1 - (A + B)) (A + B)
  have h₃ : operatorNorm (A + B) ≤ operatorNorm A + operatorNorm B := norm_add_le _ _
  have h₄ : 0 ≤ operatorNorm A + operatorNorm B := add_nonneg (norm_nonneg _) (norm_nonneg _)
  have h₅ : (operatorNorm A + operatorNorm B) ^ 2 ≤ 1 / 16 := by nlinarith
  linarith
end Products
section Commutators
theorem unitary_facts_of_mem {z : ComplexMatrix2} (hz : z ∈ specialUnitary) :
    z ∈ Matrix.unitaryGroup (Fin 2) ℂ ∧ z⁻¹ ∈ Matrix.unitaryGroup (Fin 2) ℂ ∧ z * z⁻¹ = 1 := by
  have hu : z ∈ Matrix.unitaryGroup (Fin 2) ℂ := Matrix.specialUnitaryGroup_le_unitaryGroup hz
  have hinv : z⁻¹ = star z := Matrix.inv_eq_right_inv (Matrix.mem_unitaryGroup_iff.mp hu)
  refine ⟨hu, ?_, ?_⟩
  · rw [hinv, Matrix.mem_unitaryGroup_iff, star_star]
    exact Matrix.mem_unitaryGroup_iff'.mp hu
  · rw [hinv]
    exact Matrix.mem_unitaryGroup_iff.mp hu
theorem norm_conjugateBy_sub_le (hC : NormExpLogConjugation) {z : ComplexMatrix2}
    (hz : z ∈ specialUnitary) (Y : ComplexMatrix2) :
    operatorNorm (conjugateBy z Y - Y) ≤ 2 * operatorNorm (z - 1) * operatorNorm Y := by
  obtain ⟨c₁, -, c₃, -⟩ := hC
  obtain ⟨-, hinv, hzz⟩ := unitary_facts_of_mem hz
  have hone : (1 : ComplexMatrix2) ∈ Matrix.unitaryGroup (Fin 2) ℂ := one_mem _
  have hid : conjugateBy z Y - Y = 1 * ((z - 1) * Y - Y * (z - 1)) * z⁻¹ := by
    have h₁ : 1 * ((z - 1) * Y - Y * (z - 1)) * z⁻¹ = z * Y * z⁻¹ - Y * (z * z⁻¹) := by
      noncomm_ring
    rw [h₁, hzz, mul_one]
    rfl
  rw [hid, c₃ _ _ _ hone hinv]
  have h₁ := c₁ (z - 1) Y
  have h₂ := c₁ Y (z - 1)
  have h₃ := norm_sub_le ((z - 1) * Y) (Y * (z - 1))
  nlinarith
theorem norm_conj_sub_le (hC : NormExpLogConjugation) {z : ComplexMatrix2}
    (hz : z ∈ specialUnitary) (X : ComplexMatrix2) :
    operatorNorm (z * X * z⁻¹ - X) ≤ 2 * operatorNorm (z - 1) * operatorNorm (X - 1) := by
  obtain ⟨-, -, hzz⟩ := unitary_facts_of_mem hz
  have hid : z * X * z⁻¹ - X = conjugateBy z (X - 1) - (X - 1) := by
    have h₁ : conjugateBy z (X - 1) = z * X * z⁻¹ - z * z⁻¹ := by
      show z * (X - 1) * z⁻¹ = _
      noncomm_ring
    rw [h₁, hzz]
    abel
  rw [hid]
  exact norm_conjugateBy_sub_le hC hz _
end Commutators
section Distance
theorem matExp_I_smul_mem (hdet : ∀ Z : ComplexMatrix2, (matExp Z).det = Complex.exp (fullTrace Z))
    {Y : ComplexMatrix2} (hY : Y ∈ hermitianTraceless) :
    matExp (Complex.I • Y) ∈ specialUnitary := by
  have hstar : star (Complex.I • Y) = -(Complex.I • Y) := by
    have hYs : star Y = Y := hY.1.symm
    rw [star_smul, hYs]
    simp
  have hmul : matExp (Complex.I • Y) * star (matExp (Complex.I • Y)) = 1 := by
    let +nondep : NormedAlgebra ℚ ComplexMatrix2 := .restrictScalars ℚ ℂ ComplexMatrix2
    rw [NormedSpace.star_exp, hstar,
      ← NormedSpace.exp_add_of_commute (Commute.neg_right (Commute.refl _)), add_neg_cancel,
      NormedSpace.exp_zero]
  rw [Matrix.mem_specialUnitaryGroup_iff]
  refine ⟨Matrix.mem_unitaryGroup_iff.mpr hmul, ?_⟩
  have htr : fullTrace (Complex.I • Y) = 0 := by
    have h₀ : fullTrace Y = 0 := hY.2
    simp only [fullTrace] at h₀ ⊢
    rw [Matrix.trace_smul, h₀, smul_zero]
  rw [hdet, htr, Complex.exp_zero]
theorem norm_le_norm_matExp_sub_one (hE : ExpLogEstimates) (hA : SpecialUnitaryAngleBounds)
    {Y : ComplexMatrix2} (hY : Y ∈ hermitianTraceless) (hπ : operatorNorm Y ≤ Real.pi) :
    operatorNorm Y ≤ operatorNorm (matExp (Complex.I • Y) - 1) + 1 / 24 * operatorNorm Y ^ 3 := by
  obtain ⟨-, -, -, -, -, e₆, -⟩ := hE
  obtain ⟨-, a₂, a₃, -⟩ := hA
  have hW := matExp_I_smul_mem e₆ hY
  have h₁ := (a₂ _ hW).1
  have h₂ := (a₃ Y hY).2.2.2 hπ
  rw [h₁, h₂]
  have h₃ := Real.sin_ge_sub_cube (x := operatorNorm Y / 2) (by positivity)
  nlinarith
end Distance
section Coordinates
open YangMills.Construction.Coordinates YangMills.Construction.Coordinates.ComplexCoordinates
variable {E E' : Type} [NormedAddCommGroup E] [NormedSpace ℂ E] [FiniteDimensional ℂ E]
  [NormedAddCommGroup E'] [NormedSpace ℂ E'] [FiniteDimensional ℂ E'] {N N' : ℕ}
def linearCoordinateEquiv (e : E ≃ ComplexCoordinates N) (hadd : ∀ x y, e (x + y) = e x + e y)
    (hsmul : ∀ (c : ℂ) x, e (c • x) = c • e x) : E ≃L[ℂ] ComplexCoordinates N :=
  LinearEquiv.toContinuousLinearEquiv
    { e with
      map_add' := hadd
      map_smul' := hsmul }
theorem differentiableOn_of_isHolomorphicVia
    (hH : YangMills.Construction.Coordinates.ComplexCoordinates.PowerSeriesHolomorphy.Properties)
    (e : E ≃ ComplexCoordinates N) (hadd : ∀ x y, e (x + y) = e x + e y)
    (hsmul : ∀ (c : ℂ) x, e (c • x) = c • e x)
    (e' : E' ≃ ComplexCoordinates N') (hadd' : ∀ x y, e' (x + y) = e' x + e' y)
    (hsmul' : ∀ (c : ℂ) x, e' (c • x) = c • e' x)
    {O : Set E} {f : E → E'} (hf : IsHolomorphicVia e e' O f) :
    DifferentiableOn ℂ f O := by
  have hopen : IsOpen (e '' O) := hf.1
  have hdiff := ((hH.1 N (e '' O) hopen).1 N' _ hf).2.2.1
  set L := linearCoordinateEquiv e hadd hsmul
  set L' := linearCoordinateEquiv e' hadd' hsmul'
  have hL : ∀ x, L x = e x := fun _ => rfl
  have hL' : ∀ y, L'.symm (e' y) = y := fun y => e'.symm_apply_apply y
  intro x hx
  obtain ⟨D, hD⟩ := hdiff (e x) ⟨x, hx, rfl⟩
  have hF : DifferentiableAt ℂ (e' ∘ f ∘ e.symm) (L x) :=
    (hasFDerivAt_of_restrictScalars ℝ hD rfl).differentiableAt
  have hcomp : DifferentiableAt ℂ (fun y => L'.symm ((e' ∘ f ∘ e.symm) (L y))) x :=
    L'.symm.differentiableAt.comp x (hF.comp x L.differentiableAt)
  have heq : (fun y => L'.symm ((e' ∘ f ∘ e.symm) (L y))) = f := by
    funext y
    simp [hL, hL']
  rw [heq] at hcomp
  exact hcomp.differentiableWithinAt
theorem matrixEquiv_add (x y : ComplexMatrix2) :
    matrixEquiv (x + y) = matrixEquiv x + matrixEquiv y := rfl
theorem matrixEquiv_smul (c : ℂ) (x : ComplexMatrix2) :
    matrixEquiv (c • x) = c • matrixEquiv x := rfl
def pairIndexEquiv : (Σ i : Fin 2, Fin (matrixPairComponents i).dim) ≃
    Fin (productDim matrixPairComponents) := finSigmaFinEquiv
theorem matrixPairEquiv_apply (p : ComplexMatrix2 × ComplexMatrix2)
    (x : Σ i : Fin 2, Fin (matrixPairComponents i).dim) :
    matrixPairEquiv p (pairIndexEquiv x) =
      (matrixPairComponents x.1).equiv ((finTwoArrowEquiv ComplexMatrix2).symm p x.1) x.2 := by
  let g : (Σ i : Fin 2, Fin (matrixPairComponents i).dim) → ℂ := fun y =>
    (matrixPairComponents y.1).equiv ((finTwoArrowEquiv ComplexMatrix2).symm p y.1) y.2
  have h : ∀ k, matrixPairEquiv p k = g (pairIndexEquiv.symm k) := fun _ => rfl
  rw [h, Equiv.symm_apply_apply]
theorem matrixPairEquiv_add (x y : ComplexMatrix2 × ComplexMatrix2) :
    matrixPairEquiv (x + y) = matrixPairEquiv x + matrixPairEquiv y := by
  funext k
  obtain ⟨z, rfl⟩ := pairIndexEquiv.surjective k
  show matrixPairEquiv (x + y) (pairIndexEquiv z) =
    matrixPairEquiv x (pairIndexEquiv z) + matrixPairEquiv y (pairIndexEquiv z)
  rw [matrixPairEquiv_apply, matrixPairEquiv_apply, matrixPairEquiv_apply]
  obtain ⟨i, j⟩ := z
  fin_cases i <;> rfl
theorem matrixPairEquiv_smul (c : ℂ) (x : ComplexMatrix2 × ComplexMatrix2) :
    matrixPairEquiv (c • x) = c • matrixPairEquiv x := by
  funext k
  obtain ⟨z, rfl⟩ := pairIndexEquiv.surjective k
  show matrixPairEquiv (c • x) (pairIndexEquiv z) =
    c • matrixPairEquiv x (pairIndexEquiv z)
  rw [matrixPairEquiv_apply, matrixPairEquiv_apply]
  obtain ⟨i, j⟩ := z
  fin_cases i <;> rfl
theorem differentiableOn_of_isHolomorphicVia_matrix
    (hH : YangMills.Construction.Coordinates.ComplexCoordinates.PowerSeriesHolomorphy.Properties)
    {O : Set ComplexMatrix2} {f : ComplexMatrix2 → ComplexMatrix2}
    (hf : IsHolomorphicVia matrixEquiv matrixEquiv O f) :
    DifferentiableOn ℂ f O := by apply _root_.YangMills.SharedProofs.p53137 <;> assumption
theorem differentiableOn_of_isHolomorphicVia_pair
    (hH : YangMills.Construction.Coordinates.ComplexCoordinates.PowerSeriesHolomorphy.Properties)
    {O : Set (ComplexMatrix2 × ComplexMatrix2)} {f : ComplexMatrix2 × ComplexMatrix2 → ComplexMatrix2}
    (hf : IsHolomorphicVia matrixPairEquiv matrixEquiv O f) :
    DifferentiableOn ℂ f O :=
  differentiableOn_of_isHolomorphicVia hH _ matrixPairEquiv_add matrixPairEquiv_smul _
    matrixEquiv_add matrixEquiv_smul hf
end Coordinates
section TwoMatrices
theorem norm_le_of_schwarz_each_variable {ρ M : ℝ} {f : ComplexMatrix2 × ComplexMatrix2 → ComplexMatrix2}
    (hf : DifferentiableOn ℂ f {p | operatorNorm p.1 < ρ ∧ operatorNorm p.2 < ρ})
    (hM : ∀ X Z : ComplexMatrix2, operatorNorm X < ρ → operatorNorm Z < ρ →
      operatorNorm (f (X, Z)) ≤ M)
    (hZ : ∀ Z : ComplexMatrix2, operatorNorm Z < ρ → f (0, Z) = 0)
    (hX : ∀ X : ComplexMatrix2, operatorNorm X < ρ → f (X, 0) = 0)
    {X Z : ComplexMatrix2} (hXρ : operatorNorm X < ρ) (hZρ : operatorNorm Z < ρ) :
    operatorNorm (f (X, Z)) ≤ M * (ρ ^ 2)⁻¹ * operatorNorm X * operatorNorm Z := by
  have hρ : 0 < ρ := (norm_nonneg _).trans_lt hXρ
  have first : ∀ Z' : ComplexMatrix2, operatorNorm Z' < ρ →
      operatorNorm (f (X, Z')) ≤ M / ρ * operatorNorm X := by
    intro Z' hZ'
    have hd : DifferentiableOn ℂ (fun A : ComplexMatrix2 => f (A, Z')) (ball 0 ρ) := by
      refine hf.comp (by fun_prop) ?_
      intro A hA
      exact ⟨mem_ball_zero_iff.mp hA, hZ'⟩
    have hmaps : Set.MapsTo (fun A : ComplexMatrix2 => f (A, Z')) (ball 0 ρ)
        (closedBall ((fun A : ComplexMatrix2 => f (A, Z')) 0) M) := by
      intro A hA
      simp only [hZ Z' hZ']
      rw [mem_closedBall_zero_iff]
      exact hM A Z' (mem_ball_zero_iff.mp hA) hZ'
    have hb := Complex.dist_le_div_mul_dist_of_mapsTo_ball hd hmaps
      (mem_ball_zero_iff.mpr hXρ)
    simp only [hZ Z' hZ', dist_zero_right] at hb
    exact hb
  have hd : DifferentiableOn ℂ (fun B : ComplexMatrix2 => f (X, B)) (ball 0 ρ) := by
    refine hf.comp (by fun_prop) ?_
    intro B hB
    exact ⟨hXρ, mem_ball_zero_iff.mp hB⟩
  have hmaps : Set.MapsTo (fun B : ComplexMatrix2 => f (X, B)) (ball 0 ρ)
      (closedBall ((fun B : ComplexMatrix2 => f (X, B)) 0) (M / ρ * operatorNorm X)) := by
    intro B hB
    simp only [hX X hXρ]
    rw [mem_closedBall_zero_iff]
    exact first B (mem_ball_zero_iff.mp hB)
  have hb := Complex.dist_le_div_mul_dist_of_mapsTo_ball hd hmaps (mem_ball_zero_iff.mpr hZρ)
  simp only [hX X hXρ, dist_zero_right] at hb
  calc operatorNorm (f (X, Z)) ≤ M / ρ * operatorNorm X / ρ * operatorNorm Z := hb
    _ = M * (ρ ^ 2)⁻¹ * operatorNorm X * operatorNorm Z := by
      field_simp
theorem differentiableOn_logSeries_matExp_mul
    (hH : YangMills.Construction.Coordinates.ComplexCoordinates.PowerSeriesHolomorphy.Properties)
    {A B : ComplexMatrix2 × ComplexMatrix2 → ComplexMatrix2} (hA : Differentiable ℂ A)
    (hB : Differentiable ℂ B)
    {D : Set (ComplexMatrix2 × ComplexMatrix2)}
    (hD : ∀ p ∈ D, operatorNorm (matExp (A p) * matExp (B p) - 1) < 1) :
    DifferentiableOn ℂ (fun p => logSeries (matExp (A p) * matExp (B p))) D := by
  have hexp : Differentiable ℂ matExp := fun x =>
    (differentiableOn_of_isHolomorphicVia_matrix hH hH.2.2.2.2.1 x
      (Set.mem_univ x)).differentiableAt Filter.univ_mem
  have hlog := differentiableOn_of_isHolomorphicVia_matrix hH hH.2.2.2.2.2
  exact hlog.comp ((hexp.comp hA).mul (hexp.comp hB)).differentiableOn hD
theorem matExp_mul_matExp_of_commute {x y : ComplexMatrix2} (h : Commute x y) :
    matExp x * matExp y = matExp (x + y) := by
  let +nondep : NormedAlgebra ℚ ComplexMatrix2 := .restrictScalars ℚ ℂ ComplexMatrix2
  exact (NormedSpace.exp_add_of_commute h).symm
theorem norm_logSeries_matExp_mul_sub_le (hE : ExpLogEstimates)
    (hH : YangMills.Construction.Coordinates.ComplexCoordinates.PowerSeriesHolomorphy.Properties)
    {A B : ComplexMatrix2 × ComplexMatrix2 → ComplexMatrix2} (hA : Differentiable ℂ A)
    (hB : Differentiable ℂ B)
    (hsum : ∀ X Z : ComplexMatrix2, operatorNorm X < 1 / 12 → operatorNorm Z < 1 / 12 →
      operatorNorm (A (X, Z)) + operatorNorm (B (X, Z)) ≤ 1 / 4)
    (hZ : ∀ Z : ComplexMatrix2,
      matExp (A (0, Z)) * matExp (B (0, Z)) = matExp (A (0, Z) + B (0, Z)))
    (hX : ∀ X : ComplexMatrix2,
      matExp (A (X, 0)) * matExp (B (X, 0)) = matExp (A (X, 0) + B (X, 0)))
    {X Z : ComplexMatrix2} (hX' : operatorNorm X ≤ 1 / 16) (hZ' : operatorNorm Z ≤ 1 / 16) :
    operatorNorm (logSeries (matExp (A (X, Z)) * matExp (B (X, Z))) - (A (X, Z) + B (X, Z))) ≤
      36 * operatorNorm X * operatorNorm Z := by
  have hlog : ∀ W W' : ComplexMatrix2, operatorNorm W + operatorNorm W' ≤ 1 / 4 →
      logSeries (matExp (W + W')) = W + W' := by
    intro W W' h
    have h₁ : operatorNorm (W + W') ≤ operatorNorm W + operatorNorm W' := norm_add_le _ _
    have h₂ := Real.log_two_gt_d9
    exact (hE.2.2.2.2.1 (W + W') (by linarith)).2
  have hd : DifferentiableOn ℂ (fun p => logSeries (matExp (A p) * matExp (B p)) - (A p + B p))
      {p : ComplexMatrix2 × ComplexMatrix2 | operatorNorm p.1 < 1 / 12 ∧
        operatorNorm p.2 < 1 / 12} := by
    refine (differentiableOn_logSeries_matExp_mul hH hA hB ?_).sub (hA.add hB).differentiableOn
    rintro ⟨X₁, Z₁⟩ ⟨h₁, h₂⟩
    exact (matExp_mul_matExp_estimates hE (hsum X₁ Z₁ h₁ h₂)).1
  have hb := norm_le_of_schwarz_each_variable (ρ := 1 / 12) (M := 1 / 4) hd
    (fun X₁ Z₁ h₁ h₂ => by
      have h₃ := hsum X₁ Z₁ h₁ h₂
      have h₄ : 0 ≤ operatorNorm (A (X₁, Z₁)) + operatorNorm (B (X₁, Z₁)) :=
        add_nonneg (norm_nonneg _) (norm_nonneg _)
      have h₅ := (matExp_mul_matExp_estimates hE h₃).2
      have h₆ : (operatorNorm (A (X₁, Z₁)) + operatorNorm (B (X₁, Z₁))) ^ 2 ≤ 1 / 16 := by
        nlinarith
      exact h₅.trans (by linarith))
    (fun Z₁ h₁ => by
      have h₃ := hsum 0 Z₁ (by simp) h₁
      simp only [hZ, hlog _ _ h₃, sub_self])
    (fun X₁ h₁ => by
      have h₃ := hsum X₁ 0 h₁ (by simp)
      simp only [hX, hlog _ _ h₃, sub_self])
    (lt_of_le_of_lt hX' (by norm_num)) (lt_of_le_of_lt hZ' (by norm_num))
  have h36 : (1 / 4 : ℝ) * ((1 / 12 : ℝ) ^ 2)⁻¹ = 36 := by norm_num
  rw [h36] at hb
  exact hb
theorem boundsBchRemainders_thirtySix (hE : ExpLogEstimates)
    (hH : YangMills.Construction.Coordinates.ComplexCoordinates.PowerSeriesHolomorphy.Properties) :
    BoundsBchRemainders 36 := by
  intro X Z hX hZ
  refine ⟨?_, ?_, ?_⟩
  · have h := norm_logSeries_matExp_mul_sub_le hE hH (A := Prod.fst) (B := Prod.snd)
      differentiable_fst differentiable_snd
      (fun X₁ Z₁ h₁ h₂ => by
        show operatorNorm X₁ + operatorNorm Z₁ ≤ 1 / 4
        linarith)
      (fun Z₁ => matExp_mul_matExp_of_commute (Commute.zero_left _))
      (fun X₁ => matExp_mul_matExp_of_commute (Commute.zero_right _)) hX hZ
    simpa only [bchRemainder, sub_sub] using h
  · have h := norm_logSeries_matExp_mul_sub_le hE hH (A := fun p => -p.2)
      (B := fun p => p.2 + p.1)
      differentiable_snd.neg (differentiable_snd.add differentiable_fst)
      (fun X₁ Z₁ h₁ h₂ => by
        show operatorNorm (-Z₁) + operatorNorm (Z₁ + X₁) ≤ 1 / 4
        have h₃ : operatorNorm (Z₁ + X₁) ≤ operatorNorm Z₁ + operatorNorm X₁ := norm_add_le _ _
        have h₄ : operatorNorm (-Z₁) = operatorNorm Z₁ := norm_neg _
        linarith)
      (fun Z₁ => matExp_mul_matExp_of_commute (by simp))
      (fun X₁ => matExp_mul_matExp_of_commute (by simp)) hX hZ
    simpa only [neg_add_cancel_left] using h
  · have h := norm_logSeries_matExp_mul_sub_le hE hH (A := fun p => -p.2 + p.1)
      (B := fun p => p.2)
      (differentiable_snd.neg.add differentiable_fst) differentiable_snd
      (fun X₁ Z₁ h₁ h₂ => by
        show operatorNorm (-Z₁ + X₁) + operatorNorm Z₁ ≤ 1 / 4
        have h₃ : operatorNorm (-Z₁ + X₁) ≤ operatorNorm (-Z₁) + operatorNorm X₁ :=
          norm_add_le _ _
        have h₄ : operatorNorm (-Z₁) = operatorNorm Z₁ := norm_neg _
        linarith)
      (fun Z₁ => matExp_mul_matExp_of_commute (by simp))
      (fun X₁ => matExp_mul_matExp_of_commute (by simp)) hX hZ
    have hid : -Z + X + Z = X := by abel
    simpa only [hid] using h
end TwoMatrices
theorem elementaryInequalities (hC : NormExpLogConjugation)
    (hE : ExpLogEstimates)
    (hH : YangMills.Construction.Coordinates.ComplexCoordinates.PowerSeriesHolomorphy.Properties)
    (hA : SpecialUnitaryAngleBounds) : ElementaryInequalitiesStatement := by
  refine ⟨fun n _ X => expListProduct_estimates hE n X, ?_,
    ⟨36, by norm_num, boundsBchRemainders_thirtySix hE hH⟩,
    fun z hz X _ => norm_conj_sub_le hC hz X, fun z hz Y => norm_conjugateBy_sub_le hC hz Y, ?_,
    fun Y hY h => norm_le_norm_matExp_sub_one hE hA hY h⟩
  · intro ρ M f hf hM hZ hX X Z hXρ hZρ
    exact norm_le_of_schwarz_each_variable (differentiableOn_of_isHolomorphicVia_pair hH hf)
      hM hZ hX hXρ hZρ
  · intro E E' _ _ _ _ _ _ r M f hf hb a ha
    have := FiniteDimensional.complete ℂ E'
    exact cauchy_schwarz_estimates_ball hf hb ha
end YangMills.Construction.Matrices.ComplexMatrix2.ElementaryBounds
