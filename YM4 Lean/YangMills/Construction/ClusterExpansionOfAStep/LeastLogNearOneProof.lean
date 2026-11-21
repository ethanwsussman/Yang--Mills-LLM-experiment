import YangMills.Construction.ClusterExpansionOfAStep.AnglesAlongOneDirection
import YangMills.Construction.ClusterExpansionOfAStep.LeastLogNearOne
import Mathlib
set_option autoImplicit false
noncomputable section
open scoped Quaternion
namespace YangMills.Construction.QuaternionLog
open BlockAverages
def logSeriesCoeff (k : ℕ) : ℝ := (-1) ^ (k + 1) / k
def logOnePlusSeries : FormalMultilinearSeries ℝ ℍ[ℝ] ℍ[ℝ] :=
  FormalMultilinearSeries.ofScalars ℍ[ℝ] logSeriesCoeff
theorem logOnePlusSeries_radius : logOnePlusSeries.radius = 1 := by
  have h1 : ∀ k : ℕ, 1 ≤ k → ‖logSeriesCoeff k‖ / ‖logSeriesCoeff k.succ‖ = 1 + 1 / (k : ℝ) := by
    intro k hk
    unfold logSeriesCoeff
    simp only [norm_div, norm_pow, norm_neg, norm_one, one_pow, Real.norm_natCast]
    push_cast
    field_simp
  have h2 : Filter.Tendsto (fun k : ℕ => 1 + 1 / (k : ℝ)) Filter.atTop (nhds 1) := by
    have := (tendsto_one_div_atTop_nhds_zero_nat (𝕜 := ℝ)).const_add (1 : ℝ)
    simpa using this
  have h3 : Filter.Tendsto (fun k : ℕ => ‖logSeriesCoeff k‖ / ‖logSeriesCoeff k.succ‖) Filter.atTop
      (nhds ((1 : NNReal) : ℝ)) := by
    refine (h2.congr' ?_)
    filter_upwards [Filter.eventually_ge_atTop 1] with k hk
    exact (h1 k hk).symm
  have hr := FormalMultilinearSeries.ofScalars_radius_eq_of_tendsto ℍ[ℝ] logSeriesCoeff (r := 1) one_ne_zero h3
  simpa [logOnePlusSeries] using hr
theorem analyticOnNhd_logOnePlusSeries_sum : AnalyticOnNhd ℝ logOnePlusSeries.sum (Metric.ball 0 1) := by
  have hpos : 0 < logOnePlusSeries.radius := by rw [logOnePlusSeries_radius]; exact one_pos
  have h := (logOnePlusSeries.hasFPowerSeriesOnBall hpos).analyticOnNhd
  rw [logOnePlusSeries_radius] at h
  have e : Metric.eball (0 : ℍ[ℝ]) 1 = Metric.ball 0 1 := by
    have := Metric.eball_ofReal (x := (0 : ℍ[ℝ])) (ε := 1)
    simpa using this
  rwa [e] at h
def complexSlice (n : ℍ[ℝ]) : ℂ →ₗ[ℝ] ℍ[ℝ] :=
  Complex.reLm.smulRight (1 : ℍ[ℝ]) + Complex.imLm.smulRight n
theorem complexSlice_apply (n : ℍ[ℝ]) (z : ℂ) : complexSlice n z = z.re • (1 : ℍ[ℝ]) + z.im • n := by
  simp [complexSlice]
theorem complexSlice_mul (n : ℍ[ℝ]) (hn : n * n = -1) (z w : ℂ) :
    complexSlice n (z * w) = complexSlice n z * complexSlice n w := by
  simp only [complexSlice_apply, Complex.mul_re, Complex.mul_im, add_mul, mul_add, smul_mul_assoc,
    mul_smul_comm, one_mul, mul_one, smul_smul, hn]
  module
theorem complexSlice_one (n : ℍ[ℝ]) : complexSlice n 1 = 1 := by
  simp [complexSlice_apply]
theorem complexSlice_pow (n : ℍ[ℝ]) (hn : n * n = -1) (z : ℂ) (k : ℕ) :
    complexSlice n (z ^ k) = complexSlice n z ^ k := by
  induction k with
  | zero => simp [complexSlice_one]
  | succ k ih => rw [pow_succ, pow_succ, complexSlice_mul n hn, ih]
theorem mul_self_eq_neg_one_of_norm_eq_one (x : imaginaryQuaternions) (hx : ‖x‖ = 1) :
    ((x : imaginaryQuaternions) : ℍ[ℝ]) * (x : ℍ[ℝ]) = -1 := by
  have h0 : ((x : imaginaryQuaternions) : ℍ[ℝ]).re = 0 := x.2
  have h1 : star ((x : imaginaryQuaternions) : ℍ[ℝ]) = -(x : ℍ[ℝ]) := by
    ext <;> simp [h0]
  have h2 : ((x : imaginaryQuaternions) : ℍ[ℝ]) * star ((x : imaginaryQuaternions) : ℍ[ℝ]) =
      ((Quaternion.normSq ((x : imaginaryQuaternions) : ℍ[ℝ]) : ℝ) : ℍ[ℝ]) :=
    Quaternion.self_mul_star _
  have h3 : Quaternion.normSq ((x : imaginaryQuaternions) : ℍ[ℝ]) = 1 := by
    rw [Quaternion.normSq_eq_norm_mul_self]
    have : ‖((x : imaginaryQuaternions) : ℍ[ℝ])‖ = 1 := hx
    rw [this]
    norm_num
  rw [h1, h3] at h2
  have : -(((x : imaginaryQuaternions) : ℍ[ℝ]) * (x : ℍ[ℝ])) = 1 := by
    rw [← mul_neg, h2]
    simp
  rw [← this, neg_neg]
theorem logSeriesCoeff_smul_pow (n : ℕ) (z : ℂ) :
    (-1 : ℂ) ^ (n + 1) * z ^ n / n = logSeriesCoeff n • z ^ n := by
  unfold logSeriesCoeff
  rw [Complex.real_smul]
  push_cast
  ring
theorem logOnePlusSeries_sum_expUnit_sub_one (w : imaginaryQuaternions) (hπ : ‖w‖ ≤ Real.pi)
    (h1 : ‖((expUnit w : UnitQuaternion) : ℍ[ℝ]) - 1‖ < 1) :
    logOnePlusSeries.sum (((expUnit w : UnitQuaternion) : ℍ[ℝ]) - 1) = w := by
  by_cases hw : w = 0
  · subst hw
    have e : ((expUnit 0 : UnitQuaternion) : ℍ[ℝ]) - 1 = 0 := by simp [TorusFields.expUnit_zero]
    rw [e]
    have := FormalMultilinearSeries.ofScalarsSum_zero (E := ℍ[ℝ]) logSeriesCoeff
    have h2 : logSeriesCoeff 0 = 0 := by simp [logSeriesCoeff]
    rw [h2, zero_smul] at this
    simpa [logOnePlusSeries, FormalMultilinearSeries.ofScalarsSum] using this
  have hn : ‖w‖ ≠ 0 := norm_ne_zero_iff.mpr hw
  have hpos : 0 < ‖w‖ := norm_pos_iff.mpr hw
  set θ : ℝ := ‖w‖ with hθ
  set X : imaginaryQuaternions := (θ⁻¹ : ℝ) • w with hXdef
  have hX : ‖X‖ = 1 := by
    rw [hXdef, norm_smul, norm_inv, Real.norm_eq_abs, abs_of_pos hpos, inv_mul_cancel₀ hn]
  have ew : w = θ • X := by
    rw [hXdef, smul_smul, mul_inv_cancel₀ hn, one_smul]
  have hexp : ((expUnit w : UnitQuaternion) : ℍ[ℝ]) =
      ((Real.cos θ : ℝ) : ℍ[ℝ]) + Real.sin θ • ((X : imaginaryQuaternions) : ℍ[ℝ]) := by
    conv_lhs => rw [ew]
    exact TorusFields.coe_expUnit_smul X hX θ
  set z : ℂ := Complex.exp (θ * Complex.I) - 1 with hz
  have hzre : z.re = Real.cos θ - 1 := by
    simp [hz, Complex.exp_re, Complex.exp_im]
  have hzim : z.im = Real.sin θ := by
    simp [hz, Complex.exp_re, Complex.exp_im]
  have hnsq := mul_self_eq_neg_one_of_norm_eq_one X hX
  have hmap : complexSlice X z = ((expUnit w : UnitQuaternion) : ℍ[ℝ]) - 1 := by
    have hc : ((Real.cos θ : ℝ) : ℍ[ℝ]) = Real.cos θ • (1 : ℍ[ℝ]) := by
      ext <;> simp
    rw [complexSlice_apply, hzre, hzim, hexp, sub_smul, one_smul, hc]
    abel
  have hsq : ‖z‖ ^ 2 = ‖((expUnit w : UnitQuaternion) : ℍ[ℝ]) - 1‖ ^ 2 := by
    rw [TorusFields.sq_norm_unitQuaternion_sub_one, hexp]
    have h0 : ((X : imaginaryQuaternions) : ℍ[ℝ]).re = 0 := X.2
    have hre : (((Real.cos θ : ℝ) : ℍ[ℝ]) + Real.sin θ • ((X : imaginaryQuaternions) : ℍ[ℝ])).re =
        Real.cos θ := by
      simp [h0]
    rw [hre, ← Complex.normSq_eq_norm_sq, Complex.normSq_apply, hzre, hzim]
    have := Real.sin_sq_add_cos_sq θ
    nlinarith
  have hzn : ‖z‖ < 1 := by
    have h2 : ‖z‖ = ‖((expUnit w : UnitQuaternion) : ℍ[ℝ]) - 1‖ :=
      (pow_left_inj₀ (norm_nonneg _) (norm_nonneg _) two_ne_zero).mp hsq
    rw [h2]
    exact h1
  have hs := Complex.hasSum_taylorSeries_log hzn
  have hlog : Complex.log (1 + z) = θ * Complex.I := by
    rw [hz, add_sub_cancel, Complex.log_exp]
    · simp; linarith [Real.pi_pos]
    · simpa using hπ
  rw [hlog] at hs
  have hs2 := ((complexSlice X).toContinuousLinearMap).hasSum hs
  have hterm : ∀ k : ℕ, ((complexSlice X).toContinuousLinearMap) ((-1 : ℂ) ^ (k + 1) * z ^ k / k) =
      logSeriesCoeff k • (((expUnit w : UnitQuaternion) : ℍ[ℝ]) - 1) ^ k := by
    intro k
    rw [logSeriesCoeff_smul_pow]
    simp only [LinearMap.coe_toContinuousLinearMap']
    rw [map_smul, complexSlice_pow X hnsq, hmap]
  have hfin : ((complexSlice X).toContinuousLinearMap) ((θ : ℂ) * Complex.I) = w := by
    simp only [LinearMap.coe_toContinuousLinearMap']
    rw [complexSlice_apply]
    simp
    conv_rhs => rw [ew]
    rfl
  simp only [hterm, hfin] at hs2
  have e : logOnePlusSeries.sum (((expUnit w : UnitQuaternion) : ℍ[ℝ]) - 1) =
      ∑' k, logSeriesCoeff k • (((expUnit w : UnitQuaternion) : ℍ[ℝ]) - 1) ^ k :=
    FormalMultilinearSeries.ofScalars_sum_eq logSeriesCoeff _
  rw [e, hs2.tsum_eq]
theorem minimalLogAnalyticNearOne_holds : MinimalLogAnalyticNearOne := by
  refine ⟨fun q => logOnePlusSeries.sum (q - 1), ?_, ?_⟩
  · intro q hq
    have h0 : q - 1 ∈ Metric.ball (0 : ℍ[ℝ]) 1 := by
      simpa [dist_eq_norm] using hq
    have a2 : AnalyticAt ℝ (fun q : ℍ[ℝ] => q - 1) q := analyticAt_id.sub analyticAt_const
    exact AnalyticAt.comp (f := fun q : ℍ[ℝ] => q - 1) (analyticOnNhd_logOnePlusSeries_sum _ h0) a2
  · intro g hg
    have h1 := GaugeFixing.expUnit_minimalLog g
    have h2 : ‖LumpContours.minimalLog g‖ ≤ Real.pi := GaugeFixing.norm_minimalLog_le_pi g
    have h3 := logOnePlusSeries_sum_expUnit_sub_one (LumpContours.minimalLog g) h2 (by rw [h1]; exact hg)
    rw [h1] at h3
    exact h3.symm
end YangMills.Construction.QuaternionLog
end
