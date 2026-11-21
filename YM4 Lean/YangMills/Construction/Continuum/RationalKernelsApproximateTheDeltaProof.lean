import YangMills.Construction.Continuum.RegularityAndSupportsOfTheUnitKernelsProof
import YangMills.Construction.Continuum.RationalKernelsApproximateTheDelta
import Mathlib
set_option autoImplicit false
noncomputable section
namespace YangMills.Construction.Parametrix
open MeasureTheory Filter Topology Set
namespace RationalKernel
theorem euclidNormVec_sq_eq_sum (v : Fin 4 → ℝ) :
    TorusMetric.euclidNormVec v ^ 2 = ∑ i, v i ^ 2 := by apply _root_.YangMills.Construction.Parametrix.UnitKernelSupport.euclidNormVec_sq <;> assumption
theorem integral_Ioi_cube_mul_sq_add_one_zpow :
    ∫ t in Ioi (0 : ℝ), t ^ 3 * (t ^ 2 + 1) ^ (-5 : ℤ) = 1 / 24 := by
  have hderiv : ∀ s ∈ Ici (0 : ℝ),
      HasDerivAt (fun t : ℝ => -(1 / 6 : ℝ) * ((t ^ 2 + 1) ^ 3)⁻¹ + (1 / 8 : ℝ) * ((t ^ 2 + 1) ^ 4)⁻¹)
        (s ^ 3 * (s ^ 2 + 1) ^ (-5 : ℤ)) s := by
    intro s _
    have hne : s ^ 2 + 1 ≠ 0 := by positivity
    have hin : HasDerivAt (fun t : ℝ => t ^ 2 + 1) (2 * s) s := by
      simpa using (hasDerivAt_pow 2 s).add_const 1
    have hcube := (hin.pow 3).inv (pow_ne_zero 3 hne)
    have hfourth := (hin.pow 4).inv (pow_ne_zero 4 hne)
    refine HasDerivAt.congr_deriv (show HasDerivAt
      (fun t : ℝ => -(1 / 6 : ℝ) * ((t ^ 2 + 1) ^ 3)⁻¹ + (1 / 8 : ℝ) * ((t ^ 2 + 1) ^ 4)⁻¹) _ s from
      (hcube.const_mul (-(1 / 6 : ℝ))).add (hfourth.const_mul (1 / 8 : ℝ))) ?_
    simp only [Pi.pow_apply, zpow_neg]
    norm_cast
    field_simp
    ring
  have hnonneg : ∀ s ∈ Ioi (0 : ℝ), 0 ≤ s ^ 3 * (s ^ 2 + 1) ^ (-5 : ℤ) := by
    intro s hs
    have : 0 < s := hs
    positivity
  have hgrow : Tendsto (fun t : ℝ => t ^ 2 + 1) atTop atTop :=
    tendsto_atTop_add_const_right _ _ (tendsto_pow_atTop two_ne_zero)
  have hcube : Tendsto (fun t : ℝ => ((t ^ 2 + 1) ^ 3)⁻¹) atTop (𝓝 0) :=
    tendsto_inv_atTop_zero.comp ((tendsto_pow_atTop (by norm_num)).comp hgrow)
  have hfourth : Tendsto (fun t : ℝ => ((t ^ 2 + 1) ^ 4)⁻¹) atTop (𝓝 0) :=
    tendsto_inv_atTop_zero.comp ((tendsto_pow_atTop (by norm_num)).comp hgrow)
  have hzero : Tendsto
      (fun t : ℝ => -(1 / 6 : ℝ) * ((t ^ 2 + 1) ^ 3)⁻¹ + (1 / 8 : ℝ) * ((t ^ 2 + 1) ^ 4)⁻¹)
      atTop (𝓝 0) := by
    simpa using (hcube.const_mul (-(1 / 6 : ℝ))).add (hfourth.const_mul (1 / 8 : ℝ))
  rw [integral_Ioi_of_hasDerivAt_of_nonneg' hderiv hnonneg hzero]
  norm_num
theorem integral_sq_add_one_zpow_neg_five :
    ∫ v : Fin 4 → ℝ, (TorusMetric.euclidNormVec v ^ 2 + 1) ^ (-5 : ℤ) = Real.pi ^ 2 / 12 := by
  have hpres := (EuclideanSpace.volume_preserving_symm_measurableEquiv_toLp (Fin 4)).integral_comp'
    (g := fun v : Fin 4 → ℝ => (TorusMetric.euclidNormVec v ^ 2 + 1) ^ (-5 : ℤ))
  rw [← hpres]
  have hnorm : ∀ w : EuclideanSpace ℝ (Fin 4),
      TorusMetric.euclidNormVec ((MeasurableEquiv.toLp 2 (Fin 4 → ℝ)).symm w) = ‖w‖ := by
    intro w
    simp [TorusMetric.euclidNormVec, EuclideanSpace.norm_eq, sq_abs]
  simp only [hnorm]
  have hpolar := integral_fun_norm_addHaar (volume : Measure (EuclideanSpace ℝ (Fin 4)))
    (fun t : ℝ => (t ^ 2 + 1) ^ (-5 : ℤ))
  rw [hpolar]
  have hball : (volume : Measure (EuclideanSpace ℝ (Fin 4))).real (Metric.ball 0 1) =
      Real.pi ^ 2 / 2 := by
    have hGamma : Real.Gamma ((4 : ℝ) / 2 + 1) = 2 := by
      have : ((4 : ℝ) / 2 + 1) = ((2 : ℕ) : ℝ) + 1 := by norm_num
      rw [this, Real.Gamma_nat_eq_factorial]
      norm_num [Nat.factorial]
    have hroot : Real.sqrt Real.pi ^ 4 = Real.pi ^ 2 := by
      have : Real.sqrt Real.pi ^ 2 = Real.pi := Real.sq_sqrt Real.pi_pos.le
      calc Real.sqrt Real.pi ^ 4 = (Real.sqrt Real.pi ^ 2) ^ 2 := by ring
        _ = Real.pi ^ 2 := by rw [this]
    rw [Measure.real, EuclideanSpace.volume_ball]
    simp only [Fintype.card_fin, ENNReal.ofReal_one, one_pow, one_mul, Nat.cast_ofNat]
    rw [hGamma, hroot, ENNReal.toReal_ofReal (by positivity)]
  rw [hball]
  simp only [smul_eq_mul, finrank_euclideanSpace_fin, nsmul_eq_mul]
  have hradial := integral_Ioi_cube_mul_sq_add_one_zpow
  norm_num only
  rw [show (∫ t in Ioi (0 : ℝ), t ^ 3 * (t ^ 2 + 1) ^ (-5 : ℤ)) = 1 / 24 from hradial]
  ring
end RationalKernel
open RationalKernel in
theorem rationalKernel_tendsto_delta : RationalKernelTendstoDelta := by
  rintro g hg ⟨M, hM⟩
  have hpi : (0 : ℝ) < Real.pi ^ 2 := by positivity
  set K : EuclideanFunctionals.R4 → ℝ :=
    fun v => (TorusMetric.euclidNormVec v ^ 2 + 1) ^ (-5 : ℤ) with hK
  have hKint : ∫ v, K v = Real.pi ^ 2 / 12 := integral_sq_add_one_zpow_neg_five
  have hKintegrable : Integrable K := by
    by_contra h
    rw [integral_undef h] at hKint
    have : (0 : ℝ) < Real.pi ^ 2 / 12 := by positivity
    linarith
  have hKnonneg : ∀ v, 0 ≤ K v := fun v => by
    simp only [hK]
    positivity
  set κ : ℝ := 12 / Real.pi ^ 2 with hκ
  have hκnonneg : 0 ≤ κ := by positivity
  have hrescale : ∀ t : ℝ, 0 < t →
      ∫ v : EuclideanFunctionals.R4,
          ((12 * t ^ 3 / Real.pi ^ 2 * (TorusMetric.euclidNormVec v ^ 2 + t) ^ (-5 : ℤ) : ℝ) : ℂ) * g v =
        ∫ v : EuclideanFunctionals.R4, ((κ * K v : ℝ) : ℂ) * g (Real.sqrt t • v) := by
    intro t ht
    set F : EuclideanFunctionals.R4 → ℂ := fun v =>
      ((12 * t ^ 3 / Real.pi ^ 2 * (TorusMetric.euclidNormVec v ^ 2 + t) ^ (-5 : ℤ) : ℝ) : ℂ) * g v
      with hF
    have hsqrt : Real.sqrt t ^ 2 = t := Real.sq_sqrt ht.le
    have hsubst := Measure.integral_comp_smul (volume : Measure EuclideanFunctionals.R4) F (Real.sqrt t)
    have hdim : Module.finrank ℝ EuclideanFunctionals.R4 = 4 := by simp [EuclideanFunctionals.R4]
    have hsqrt4 : Real.sqrt t ^ 4 = t ^ 2 := by
      calc Real.sqrt t ^ 4 = (Real.sqrt t ^ 2) ^ 2 := by ring
        _ = t ^ 2 := by rw [hsqrt]
    rw [hdim, hsqrt4, abs_of_pos (by positivity)] at hsubst
    have hpoint : ∀ v : EuclideanFunctionals.R4, ((κ * K v : ℝ) : ℂ) * g (Real.sqrt t • v) =
        ((t ^ 2 : ℝ) : ℂ) * F (Real.sqrt t • v) := by
      intro v
      have hscale : TorusMetric.euclidNormVec (Real.sqrt t • v) ^ 2 =
          t * TorusMetric.euclidNormVec v ^ 2 := by
        rw [euclidNormVec_sq_eq_sum, euclidNormVec_sq_eq_sum, Finset.mul_sum]
        refine Finset.sum_congr rfl fun i _ => ?_
        rw [Pi.smul_apply, smul_eq_mul, mul_pow, hsqrt]
      simp only [hF, hscale, hK, hκ]
      rw [← mul_assoc, ← Complex.ofReal_mul]
      congr 2
      have hsqnn : 0 ≤ TorusMetric.euclidNormVec v ^ 2 := sq_nonneg _
      have hfactor : t * TorusMetric.euclidNormVec v ^ 2 + t =
          t * (TorusMetric.euclidNormVec v ^ 2 + 1) := by ring
      rw [hfactor, mul_zpow, zpow_neg, zpow_neg]
      norm_cast
      have : TorusMetric.euclidNormVec v ^ 2 + 1 ≠ 0 := by positivity
      field_simp
    simp only [hpoint]
    rw [integral_const_mul, hsubst, Complex.real_smul]
    have htC : (t : ℂ) ≠ 0 := by exact_mod_cast ht.ne'
    push_cast
    field_simp
  have hconv : Tendsto
      (fun t : ℝ => ∫ v : EuclideanFunctionals.R4, ((κ * K v : ℝ) : ℂ) * g (Real.sqrt t • v))
      (𝓝[>] 0) (𝓝 (∫ v : EuclideanFunctionals.R4, ((κ * K v : ℝ) : ℂ) * g 0)) := by
    refine tendsto_integral_filter_of_dominated_convergence (fun v => κ * K v * M) ?_ ?_ ?_ ?_
    · refine Eventually.of_forall fun t => ?_
      have hmeas : AEStronglyMeasurable (fun v : EuclideanFunctionals.R4 => ((κ * K v : ℝ) : ℂ)) volume :=
        Complex.continuous_ofReal.comp_aestronglyMeasurable (hKintegrable.1.const_mul κ)
      have hcont : Continuous fun v : EuclideanFunctionals.R4 => g (Real.sqrt t • v) := by fun_prop
      exact hmeas.mul hcont.aestronglyMeasurable
    · refine Eventually.of_forall fun t => Eventually.of_forall fun v => ?_
      rw [norm_mul, Complex.norm_real, Real.norm_of_nonneg (mul_nonneg hκnonneg (hKnonneg v))]
      exact mul_le_mul_of_nonneg_left (hM _) (mul_nonneg hκnonneg (hKnonneg v))
    · exact (hKintegrable.const_mul κ).mul_const M
    · refine Eventually.of_forall fun v => ?_
      have hcont : Continuous fun t : ℝ => g (Real.sqrt t • v) := by fun_prop
      have hat := (hcont.tendsto 0).mono_left (nhdsWithin_le_nhds (s := Ioi 0))
      simp only [Real.sqrt_zero, zero_smul] at hat
      exact tendsto_const_nhds.mul hat
  have hmass : ∫ v : EuclideanFunctionals.R4, ((κ * K v : ℝ) : ℂ) * g 0 = g 0 := by
    rw [integral_mul_const, integral_complex_ofReal, integral_const_mul, hKint, hκ]
    have : (12 / Real.pi ^ 2 * (Real.pi ^ 2 / 12) : ℝ) = 1 := by field_simp
    rw [this]
    simp
  rw [hmass] at hconv
  exact hconv.congr' (eventually_mem_nhdsWithin.mono fun t ht => (hrescale t ht).symm)
end YangMills.Construction.Parametrix
