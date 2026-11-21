import YangMills.Construction.Continuum.RegularityAndSupportsOfTheUnitKernelsProof
import YangMills.Construction.LawInAState.HatsSumToTheFreeKernelProof
import YangMills.Construction.QuaternionicWilsonModel.WhatTheTopGivesAtEveryCouplingProof
import YangMills.Construction.Torus.BallOfTheTorusAndTheBallOverIt
import YangMills.Construction.Torus.CellsOfATranslatedLatticeAndBallsOfTheTorus
import YangMills.Construction.Torus.CollinearQuadruples
import YangMills.Construction.Torus.CoveringMapIntegralAndVolumeOnTheTorus
import YangMills.Construction.Torus.GeometryAndFreeKernelOfATestPairProof
import YangMills.Construction.Torus.GeometryOfASeparatedQuadruple
import Mathlib
set_option autoImplicit false
noncomputable section
namespace YangMills.Construction
open MeasureTheory Set Filter TorusMetric TestFunctions TorusMeasure PlaquetteSupports
namespace QuadrupleClasses.Collinear
theorem euclidNormVec_eq_norm (w : Fin 4 → ℝ) :
    euclidNormVec w = ‖(WithLp.toLp 2 w : EuclideanSpace ℝ (Fin 4))‖ := by apply _root_.YangMills.Construction.AmbientPoints.euclidNormVec_eq_norm <;> assumption
theorem euclidNormVec_nonneg (w : Fin 4 → ℝ) : 0 ≤ euclidNormVec w := Real.sqrt_nonneg _
theorem euclidNormVec_sub_le (p q : Fin 4 → ℝ) :
    euclidNormVec (p - q) ≤ euclidNormVec p + euclidNormVec q := by
  simp only [euclidNormVec_eq_norm, WithLp.toLp_sub]
  exact norm_sub_le _ _
theorem euclidNormVec_smul (r : ℝ) (p : Fin 4 → ℝ) :
    euclidNormVec (r • p) = |r| * euclidNormVec p := by apply _root_.YangMills.SharedProofs.p37834 <;> assumption
theorem euclidNormVec_sq (w : Fin 4 → ℝ) : euclidNormVec w ^ 2 = ∑ μ, w μ ^ 2 := by apply _root_.YangMills.Construction.Parametrix.UnitKernelSupport.euclidNormVec_sq <;> assumption
theorem abs_euclidNormVec_sub_le (p q : Fin 4 → ℝ) :
    |euclidNormVec p - euclidNormVec q| ≤ euclidNormVec (p - q) := by apply _root_.YangMills.DeltaSharedProofs.p501537 <;> assumption
theorem isClosed_closedBallR4 (x : Fin 4 → ℝ) (r : ℝ) : IsClosed (closedBallR4 x r) := by apply _root_.YangMills.Construction.TestPairs.isClosed_closedBallR4 <;> assumption
theorem sum_sq_eq_one_of_unit {u : Fin 4 → ℝ} (hu : euclidNormVec u = 1) :
    ∑ μ, u μ ^ 2 = 1 := by
  rw [← euclidNormVec_sq, hu]
  norm_num
theorem euclidNormVec_orthProj_le {u : Fin 4 → ℝ} (hu : euclidNormVec u = 1) (p : Fin 4 → ℝ) :
    euclidNormVec (p - dotProduct p u • u) ≤ euclidNormVec p := by
  have hu2 := sum_sq_eq_one_of_unit hu
  apply Real.sqrt_le_sqrt
  set r := dotProduct p u with hr
  have hdot : ∑ μ, p μ * u μ = r := by simp [hr, dotProduct]
  have hexp : ∑ μ, (p - r • u) μ ^ 2 =
      ∑ μ, p μ ^ 2 - 2 * r * (∑ μ, p μ * u μ) + r ^ 2 * ∑ μ, u μ ^ 2 := by
    simp only [Fin.sum_univ_four, Pi.sub_apply, Pi.smul_apply, smul_eq_mul]
    ring
  rw [hexp, hdot, hu2]
  nlinarith [sq_nonneg r]
theorem orthProj_of_decomposition {u : Fin 4 → ℝ} (hu : euclidNormVec u = 1) (r : ℝ)
    (p q : Fin 4 → ℝ) :
    (r • u + p - q) - dotProduct (r • u + p - q) u • u =
      (p - dotProduct p u • u) - (q - dotProduct q u • u) := by
  have hu2 := sum_sq_eq_one_of_unit hu
  have hdot : dotProduct (r • u + p - q) u = r + dotProduct p u - dotProduct q u := by
    simp only [dotProduct, Fin.sum_univ_four, Pi.add_apply, Pi.sub_apply, Pi.smul_apply,
      smul_eq_mul] at hu2 ⊢
    linear_combination r * hu2
  rw [hdot]
  funext μ
  simp only [Pi.add_apply, Pi.sub_apply, Pi.smul_apply, smul_eq_mul]
  ring
theorem isShapeAxis_of_geometry (hR4 : QuadrupleGeometry.GeometryOnR4) {d ϑ : ℝ}
    (hds : IsScaleShape d ϑ) : IsShapeAxisOfCollinearCentres d ϑ := by
  intro g u c hg haxis hsupp
  refine ⟨haxis.1, fun i j hij x hx y hy => ?_⟩
  obtain ⟨r, hr⟩ := haxis.2 i j
  have hsep : d ≤ euclidNormVec (x - y) :=
    ((hR4 d ϑ hds.1 hds.2 g hg).2.1.1 i j hij x hx y hy).1
  have hsplit : x - y = r • u + (x - c i) - (y - c j) := by
    rw [← hr]
    abel
  have hx16 : euclidNormVec (x - c i) ≤ d / 16 := hsupp i hx
  have hy16 : euclidNormVec (y - c j) ≤ d / 16 := hsupp j hy
  have hproj := orthProj_of_decomposition haxis.1 r (x - c i) (y - c j)
  rw [← hsplit] at hproj
  rw [hproj]
  have htri := euclidNormVec_sub_le ((x - c i) - dotProduct (x - c i) u • u)
    ((y - c j) - dotProduct (y - c j) u • u)
  have hpx := euclidNormVec_orthProj_le haxis.1 (x - c i)
  have hpy := euclidNormVec_orthProj_le haxis.1 (y - c j)
  linarith
theorem nestedClassesR4_holds (hR4 : QuadrupleGeometry.GeometryOnR4) {d ϑ : ℝ}
    (hds : IsScaleShape d ϑ) : NestedClassesR4 d ϑ := by
  refine ⟨?_, fun g hg => hg.1⟩
  rintro g ⟨hg, c, ⟨u, hu⟩, hc⟩
  exact ⟨hg, hg, u, isShapeAxis_of_geometry hR4 hds g u c hg hu hc⟩
theorem preimage_toLp_closedBall (x : Fin 4 → ℝ) (r : ℝ) :
    (WithLp.toLp 2 : (Fin 4 → ℝ) → EuclideanSpace ℝ (Fin 4)) ⁻¹'
        Metric.closedBall (WithLp.toLp 2 x) r = closedBallR4 x r := by
  ext y
  simp only [mem_preimage, Metric.mem_closedBall, dist_eq_norm, closedBallR4, mem_ofPred_eq,
    euclidNormVec_eq_norm, WithLp.toLp_sub]
theorem volume_closedBallR4 (x : Fin 4 → ℝ) {r : ℝ} (hr : 0 < r) :
    volume (closedBallR4 x r) = ENNReal.ofReal (omega4 * r ^ 4) := by
  rw [← preimage_toLp_closedBall, (PiLp.volume_preserving_toLp (Fin 4)).measure_preimage
    measurableSet_closedBall.nullMeasurableSet,
    InnerProductSpace.volume_closedBall_of_dim_even (k := 2) (by simp)]
  rw [← ENNReal.ofReal_pow hr.le, ← ENNReal.ofReal_mul (by positivity)]
  congr 1
  simp [omega4, Nat.factorial]
  ring
def bumpProfile (ρ : ℝ) : ℝ := max (1 - ρ ^ 2) 0 ^ 2
def radialBump (d : ℝ) (x : Fin 4 → ℝ) : ℝ := bumpProfile (16 / d * euclidNormVec x)
theorem bumpProfile_nonneg (ρ : ℝ) : 0 ≤ bumpProfile ρ := sq_nonneg _
theorem bumpProfile_le_one (ρ : ℝ) : bumpProfile ρ ≤ 1 := by
  have hlo : 0 ≤ max (1 - ρ ^ 2) 0 := le_max_right _ _
  have hhi : max (1 - ρ ^ 2) 0 ≤ 1 := max_le (by nlinarith [sq_nonneg ρ]) zero_le_one
  unfold bumpProfile
  nlinarith
theorem bumpProfile_of_sq_le_one {ρ : ℝ} (h : ρ ^ 2 ≤ 1) :
    bumpProfile ρ = (1 - ρ ^ 2) ^ 2 := by
  unfold bumpProfile
  rw [max_eq_left (by linarith)]
theorem bumpProfile_of_one_le_sq {ρ : ℝ} (h : 1 ≤ ρ ^ 2) : bumpProfile ρ = 0 := by
  unfold bumpProfile
  rw [max_eq_right (by linarith)]
  norm_num
theorem bumpProfile_sub_le {ρ σ : ℝ} (h0 : 0 ≤ ρ) (h : ρ ≤ σ) :
    |bumpProfile ρ - bumpProfile σ| ≤ 2 * (σ - ρ) := by
  rcases le_or_gt 1 ρ with hρ1 | hρ1
  · rw [bumpProfile_of_one_le_sq (by nlinarith), bumpProfile_of_one_le_sq (by nlinarith)]
    simp only [sub_self, abs_zero]
    linarith
  rcases le_or_gt 1 σ with hσ1 | hσ1
  · rw [bumpProfile_of_sq_le_one (by nlinarith), bumpProfile_of_one_le_sq (by nlinarith), sub_zero,
      abs_of_nonneg (sq_nonneg _)]
    have hkey : (1 - ρ ^ 2) ^ 2 ≤ 2 * (1 - ρ) := by
      have hcub : (1 - ρ) * (1 + ρ) ^ 2 ≤ 2 := by
        nlinarith [mul_nonneg h0 (sq_nonneg (ρ - 1 / 3)), sq_nonneg ρ, sq_nonneg (ρ - 1 / 3)]
      have hpos : 0 ≤ 1 - ρ := by linarith
      have hfact : (1 - ρ ^ 2) ^ 2 = (1 - ρ) * ((1 - ρ) * (1 + ρ) ^ 2) := by ring
      rw [hfact]
      nlinarith
    linarith
  · have hρsq : ρ ^ 2 ≤ 1 := by nlinarith
    have hσsq : σ ^ 2 ≤ 1 := by nlinarith
    rw [bumpProfile_of_sq_le_one hρsq, bumpProfile_of_sq_le_one hσsq]
    have hsum : 0 ≤ ρ + σ := by linarith
    have hprod : (ρ + σ) * (2 - ρ ^ 2 - σ ^ 2) ≤ 2 := by
      have hqm : (ρ + σ) ^ 2 / 2 ≤ ρ ^ 2 + σ ^ 2 := by nlinarith [sq_nonneg (ρ - σ)]
      have hmul := mul_le_mul_of_nonneg_left hqm hsum
      nlinarith [mul_nonneg hsum (sq_nonneg (ρ + σ - 6 / 5)), sq_nonneg (ρ + σ - 17 / 15)]
    have hprod0 : 0 ≤ (ρ + σ) * (2 - ρ ^ 2 - σ ^ 2) := mul_nonneg hsum (by linarith)
    have hdiff : (1 - ρ ^ 2) ^ 2 - (1 - σ ^ 2) ^ 2 =
        (σ - ρ) * ((ρ + σ) * (2 - ρ ^ 2 - σ ^ 2)) := by ring
    have hgap : 0 ≤ σ - ρ := by linarith
    rw [hdiff, abs_of_nonneg (mul_nonneg hgap hprod0)]
    nlinarith
theorem abs_bumpProfile_sub_le {ρ σ : ℝ} (hρ : 0 ≤ ρ) (hσ : 0 ≤ σ) :
    |bumpProfile ρ - bumpProfile σ| ≤ 2 * |ρ - σ| := by
  rcases le_total ρ σ with h | h
  · rw [abs_of_nonpos (sub_nonpos.2 h)]
    have := bumpProfile_sub_le hρ h
    linarith
  · rw [abs_sub_comm, abs_of_nonneg (sub_nonneg.2 h)]
    have := bumpProfile_sub_le hσ h
    linarith
theorem radialBump_nonneg (d : ℝ) (x : Fin 4 → ℝ) : 0 ≤ radialBump d x := bumpProfile_nonneg _
theorem radialBump_le_one (d : ℝ) (x : Fin 4 → ℝ) : radialBump d x ≤ 1 := bumpProfile_le_one _
theorem radialBump_zero (d : ℝ) : radialBump d 0 = 1 := by
  have : euclidNormVec 0 = 0 := by simp [euclidNormVec]
  simp [radialBump, this, bumpProfile]
theorem radialBump_eq_zero {d : ℝ} (hd : 0 < d) {x : Fin 4 → ℝ}
    (hx : d / 16 ≤ euclidNormVec x) : radialBump d x = 0 := by
  apply bumpProfile_of_one_le_sq
  have hge : 1 ≤ 16 / d * euclidNormVec x := by
    rw [div_mul_eq_mul_div, le_div_iff₀ hd]
    linarith
  nlinarith
theorem radialBump_lipschitz {d : ℝ} (hd : 0 < d) (x y : Fin 4 → ℝ) :
    |radialBump d x - radialBump d y| ≤ 32 / d * euclidNormVec (x - y) := by
  have hk : 0 ≤ 16 / d := by positivity
  have hprof := abs_bumpProfile_sub_le (mul_nonneg hk (euclidNormVec_nonneg x))
    (mul_nonneg hk (euclidNormVec_nonneg y))
  have hrev := abs_euclidNormVec_sub_le x y
  have hfac : |16 / d * euclidNormVec x - 16 / d * euclidNormVec y| =
      16 / d * |euclidNormVec x - euclidNormVec y| := by
    rw [← mul_sub, abs_mul, abs_of_nonneg hk]
  have hscaled := mul_le_mul_of_nonneg_left hrev hk
  have htwo : 32 / d = 2 * (16 / d) := by ring
  unfold radialBump
  rw [hfac] at hprof
  rw [htwo]
  nlinarith
theorem hasDerivAt_sq_max_zero (σ : ℝ) :
    HasDerivAt (fun σ : ℝ => max σ 0 ^ 2) (2 * max σ 0) σ := by
  rcases lt_trichotomy σ 0 with h | h | h
  · rw [max_eq_right h.le, mul_zero]
    refine (hasDerivAt_const σ (0 : ℝ)).congr_of_eventuallyEq ?_
    filter_upwards [Iio_mem_nhds h] with τ hτ
    rw [max_eq_right (le_of_lt hτ)]
    norm_num
  · subst h
    rw [max_self, mul_zero, hasDerivAt_iff_isLittleO_nhds_zero]
    have hbig : (fun h : ℝ => max (0 + h) 0 ^ 2 - max (0 : ℝ) 0 ^ 2 - h • (0 : ℝ)) =O[nhds 0]
        fun h : ℝ => h ^ 2 := by
      refine Asymptotics.IsBigO.of_bound 1 (Eventually.of_forall fun h => ?_)
      have hz : (0 : ℝ) ^ 2 = 0 := by norm_num
      rw [max_self, zero_add, smul_zero, sub_zero, hz, sub_zero, Real.norm_eq_abs,
        Real.norm_eq_abs, abs_of_nonneg (sq_nonneg _), abs_of_nonneg (sq_nonneg h), one_mul]
      rcases le_total h 0 with hh | hh
      · rw [max_eq_right hh]
        nlinarith [sq_nonneg h]
      · rw [max_eq_left hh]
    exact hbig.trans_isLittleO (Asymptotics.isLittleO_pow_id (by norm_num))
  · rw [max_eq_left h.le]
    refine (hasDerivAt_pow 2 σ).congr_of_eventuallyEq ?_ |>.congr_deriv (by norm_num)
    filter_upwards [Ioi_mem_nhds h] with τ hτ
    rw [max_eq_left (le_of_lt hτ)]
theorem contDiff_sq_max_zero : ContDiff ℝ 1 (fun σ : ℝ => max σ 0 ^ 2) := by
  rw [contDiff_one_iff_deriv]
  refine ⟨fun σ => (hasDerivAt_sq_max_zero σ).differentiableAt, ?_⟩
  have : deriv (fun σ : ℝ => max σ 0 ^ 2) = fun σ => 2 * max σ 0 :=
    funext fun σ => (hasDerivAt_sq_max_zero σ).deriv
  rw [this]
  fun_prop
theorem contDiff_radialBump (d : ℝ) : ContDiff ℝ 1 (radialBump d) := by
  have h : radialBump d = (fun σ : ℝ => max σ 0 ^ 2) ∘
      fun x : Fin 4 → ℝ => 1 - (16 / d) ^ 2 * ∑ μ, x μ ^ 2 := by
    funext x
    simp only [radialBump, bumpProfile, Function.comp, mul_pow, euclidNormVec_sq]
  rw [h]
  refine contDiff_sq_max_zero.comp ?_
  fun_prop
theorem integral_radial_profile {d : ℝ} (hd : 0 < d) :
    ∫ y in (0 : ℝ)..(d / 16), y ^ 3 * (1 - (16 / d * y) ^ 2) ^ 2 = (d / 16) ^ 4 / 24 := by
  set κ := 16 / d with hκ
  have hF : ∀ y : ℝ, HasDerivAt (fun y : ℝ => y ^ 4 / 4 - κ ^ 2 * y ^ 6 / 3 + κ ^ 4 * y ^ 8 / 8)
      (y ^ 3 * (1 - (κ * y) ^ 2) ^ 2) y := by
    intro y
    have h := (((hasDerivAt_pow 4 y).div_const 4).sub
      (((hasDerivAt_pow 6 y).const_mul (κ ^ 2)).div_const 3)).add
      (((hasDerivAt_pow 8 y).const_mul (κ ^ 4)).div_const 8)
    have h2 : HasDerivAt (fun y : ℝ => y ^ 4 / 4 - κ ^ 2 * y ^ 6 / 3 + κ ^ 4 * y ^ 8 / 8) _ y := h
    refine h2.congr_deriv ?_
    norm_num
    ring
  rw [intervalIntegral.integral_eq_sub_of_hasDerivAt (fun y _ => hF y)
    (Continuous.intervalIntegrable (by fun_prop) _ _)]
  have hr : κ * (d / 16) = 1 := by
    rw [hκ]
    field_simp
  have e6 : κ ^ 2 * (d / 16) ^ 6 = (d / 16) ^ 4 := by
    have : κ ^ 2 * (d / 16) ^ 6 = (κ * (d / 16)) ^ 2 * (d / 16) ^ 4 := by ring
    rw [this, hr]
    ring
  have e8 : κ ^ 4 * (d / 16) ^ 8 = (d / 16) ^ 4 := by
    have : κ ^ 4 * (d / 16) ^ 8 = (κ * (d / 16)) ^ 4 * (d / 16) ^ 4 := by ring
    rw [this, hr]
    ring
  rw [e6, e8]
  ring
theorem integral_Ioi_radial_profile {d : ℝ} (hd : 0 < d) :
    ∫ y in Ioi (0 : ℝ), y ^ 3 • bumpProfile (16 / d * y) = (d / 16) ^ 4 / 24 := by
  have hr : 0 < d / 16 := by positivity
  rw [setIntegral_eq_of_subset_of_forall_sdiff_eq_zero (s := Ioc 0 (d / 16)) measurableSet_Ioi
    Ioc_subset_Ioi_self ?_]
  · rw [← integral_radial_profile hd, intervalIntegral.integral_of_le hr.le]
    refine setIntegral_congr_fun measurableSet_Ioc fun y hy => ?_
    have h1 : 16 / d * y ≤ 1 := by
      rw [div_mul_eq_mul_div, div_le_one hd]
      linarith [hy.2]
    have h0 : 0 ≤ 16 / d * y := mul_nonneg (by positivity) hy.1.le
    have : (16 / d * y) ^ 2 ≤ 1 := by nlinarith
    simp only [smul_eq_mul]
    rw [bumpProfile_of_sq_le_one this]
  · intro y hy
    have hy' : d / 16 < y := by
      by_contra hc
      exact hy.2 ⟨hy.1, not_lt.1 hc⟩
    have h1 : 1 ≤ 16 / d * y := by
      rw [div_mul_eq_mul_div, le_div_iff₀ hd]
      linarith
    rw [bumpProfile_of_one_le_sq (by nlinarith), smul_zero]
theorem integral_radialBump {d : ℝ} (hd : 0 < d) :
    ∫ x, radialBump d x = omega4 * (d / 16) ^ 4 / 6 := by
  have h1 := (EuclideanSpace.volume_preserving_symm_measurableEquiv_toLp (Fin 4)).integral_comp'
    (radialBump d)
  rw [← h1]
  have h2 : ∀ y : EuclideanSpace ℝ (Fin 4),
      radialBump d ((MeasurableEquiv.toLp 2 (Fin 4 → ℝ)).symm y) =
        (fun ρ => bumpProfile (16 / d * ρ)) ‖y‖ := by
    intro y
    simp only [radialBump, euclidNormVec_eq_norm]
    rfl
  simp_rw [h2]
  rw [integral_fun_norm_addHaar (volume : Measure (EuclideanSpace ℝ (Fin 4)))
    (fun ρ => bumpProfile (16 / d * ρ))]
  have hf : Module.finrank ℝ (EuclideanSpace ℝ (Fin 4)) = 4 := by simp
  have hv : (volume : Measure (EuclideanSpace ℝ (Fin 4))).real (Metric.ball 0 1) = omega4 := by
    rw [Measure.real, InnerProductSpace.volume_ball_of_dim_even (k := 2) (by simp)]
    simp [omega4, Nat.factorial]
    positivity
  rw [hf, hv]
  simp only [show 4 - 1 = 3 from rfl]
  rw [integral_Ioi_radial_profile hd]
  simp only [nsmul_eq_mul, smul_eq_mul]
  push_cast
  ring
theorem collinearThetaBound_pos : 0 < collinearThetaBound := by
  unfold collinearThetaBound omega4
  positivity
theorem collinearThetaBound_lt : collinearThetaBound < 1 / 32 := by
  have hpi := Real.pi_le_four
  have hpi0 := Real.pi_pos
  unfold collinearThetaBound omega4
  rw [div_lt_iff₀ (by norm_num)]
  nlinarith
theorem collinearThetaBound_le_one : collinearThetaBound ≤ 1 := by
  have := collinearThetaBound_lt
  linarith
theorem uniformNorm_shifted_bump (d : ℝ) (c : Fin 4 → ℝ) :
    uniformNorm (fun x => radialBump d (x - c)) = 1 := by
  have hb : ∀ x, ‖radialBump d (x - c)‖ ≤ 1 := fun x => by
    rw [Real.norm_eq_abs, abs_of_nonneg (radialBump_nonneg _ _)]
    exact radialBump_le_one _ _
  apply le_antisymm
  · exact ciSup_le hb
  · refine le_ciSup_of_le ⟨1, ?_⟩ c ?_
    · rintro _ ⟨x, rfl⟩
      exact hb x
    · simp [radialBump_zero]
theorem tsupport_shifted_bump_subset {d : ℝ} (hd : 0 < d) (c : Fin 4 → ℝ) :
    tsupport (fun x => radialBump d (x - c)) ⊆ closedBallR4 c (d / 16) := by
  refine closure_minimal ?_ (isClosed_closedBallR4 _ _)
  intro x hx
  by_contra hc
  exact hx (radialBump_eq_zero hd (le_of_lt (not_le.1 hc)))
theorem mem_tsupport_shifted_bump (d : ℝ) (c : Fin 4 → ℝ) :
    c ∈ tsupport (fun x => radialBump d (x - c)) :=
  subset_tsupport _ (by simp [Function.mem_support, radialBump_zero])
theorem isLipschitzFor_shifted_bump {d : ℝ} (hd : 0 < d) (c : Fin 4 → ℝ) :
    IsLipschitzFor euclidDistR4 (fun x => radialBump d (x - c)) := by
  refine ⟨32 / d, by positivity, fun x y => ?_⟩
  have h := radialBump_lipschitz hd (x - c) (y - c)
  rw [sub_sub_sub_cancel_right] at h
  exact h
theorem isShapedBump_shifted_bump {d ϑ : ℝ} (hd : 0 < d) (hϑ0 : 0 < ϑ)
    (hϑ : ϑ ≤ collinearThetaBound) (c : Fin 4 → ℝ) :
    IsShapedBump euclidDistR4 closedBallR4 integralR4 d ϑ c
      (fun x => radialBump d (x - c)) := by
  have hsub : closedBallR4 c (d / 16) ⊆ closedBallR4 c d := by
    intro y hy
    have h1 : euclidNormVec (y - c) ≤ d / 16 := hy
    show euclidNormVec (y - c) ≤ d
    linarith
  refine ⟨isLipschitzFor_shifted_bump hd c, fun y => radialBump_nonneg _ _,
    ⟨c, by simp [radialBump_zero]⟩, (tsupport_shifted_bump_subset hd c).trans hsub, ?_, ?_⟩
  · rw [uniformNorm_shifted_bump, integralR4, integral_sub_right_eq_self (fun x => radialBump d x) c,
      integral_radialBump hd]
    have h := mul_le_mul_of_nonneg_right hϑ (by positivity : 0 ≤ d ^ 4)
    have h2 : collinearThetaBound * d ^ 4 = omega4 * (d / 16) ^ 4 / 6 := by
      unfold collinearThetaBound
      ring
    rw [mul_one, ← h2]
    exact h
  · rw [uniformNorm_shifted_bump]
    have hmem : 32 / d ∈ {C : ℝ | 0 ≤ C ∧ ∀ x y, ‖(fun x => radialBump d (x - c)) x -
        (fun x => radialBump d (x - c)) y‖ ≤ C * euclidDistR4 x y} := by
      refine ⟨by positivity, fun x y => ?_⟩
      have h := radialBump_lipschitz hd (x - c) (y - c)
      rw [sub_sub_sub_cancel_right] at h
      exact h
    have h1 : bestLipschitzConstant euclidDistR4 (fun x => radialBump d (x - c)) ≤ 32 / d :=
      csInf_le ⟨0, fun C hC => hC.1⟩ hmem
    refine h1.trans ?_
    rw [div_le_div_iff₀ hd (by positivity)]
    have := collinearThetaBound_lt
    have h3 : 32 * ϑ ≤ 1 := by linarith
    nlinarith
def collinearCentres (c₁ u : Fin 4 → ℝ) (d : ℝ) : Fin 4 → Fin 4 → ℝ :=
  fun i => c₁ + (2 * ((i : ℕ) : ℝ) * d) • u
theorem collinearCentres_sub (c₁ u : Fin 4 → ℝ) (d : ℝ) (i j : Fin 4) :
    collinearCentres c₁ u d i - collinearCentres c₁ u d j =
      (2 * (((i : ℕ) : ℝ) - ((j : ℕ) : ℝ)) * d) • u := by
  funext μ
  simp only [collinearCentres, Pi.sub_apply, Pi.add_apply, Pi.smul_apply, smul_eq_mul]
  ring
theorem index_gap_bounds {i j : Fin 4} (h : i ≠ j) :
    1 ≤ |((i : ℕ) : ℝ) - ((j : ℕ) : ℝ)| ∧ |((i : ℕ) : ℝ) - ((j : ℕ) : ℝ)| ≤ 3 := by apply _root_.YangMills.Construction.NonGaussianLimits.fin_four_index_gap <;> assumption
theorem dist_collinearCentres {c₁ u : Fin 4 → ℝ} {d : ℝ} (hd : 0 < d)
    (hu : euclidNormVec u = 1) {i j : Fin 4} (h : i ≠ j) :
    2 * d ≤ euclidNormVec (collinearCentres c₁ u d i - collinearCentres c₁ u d j) ∧
      euclidNormVec (collinearCentres c₁ u d i - collinearCentres c₁ u d j) ≤ 6 * d := by
  rw [collinearCentres_sub, euclidNormVec_smul, hu, mul_one, abs_mul, abs_mul, abs_of_pos hd]
  have := index_gap_bounds h
  norm_num
  constructor <;> nlinarith [this.1, this.2]
theorem translateFamily_mem {d ϑ : ℝ} (hds : IsScaleShape d ϑ) (hϑ : ϑ ≤ collinearThetaBound)
    (c₁ u : Fin 4 → ℝ) (hu : euclidNormVec u = 1) :
    translateFamily (radialBump d) (collinearCentres c₁ u d) ∈ collinearQuadsR4 d ϑ := by
  have hd := hds.1
  refine ⟨⟨hds, fun i => ⟨isLipschitzFor_shifted_bump hd _, fun y => radialBump_nonneg _ _⟩,
    fun i j hij => ?_⟩, collinearCentres c₁ u d,
    ⟨u, hu, fun i j => ⟨_, collinearCentres_sub c₁ u d i j⟩⟩,
    fun i => tsupport_shifted_bump_subset hd _⟩
  refine ⟨collinearCentres c₁ u d i, collinearCentres c₁ u d j,
    isShapedBump_shifted_bump hd hds.2.1 hϑ _, isShapedBump_shifted_bump hd hds.2.1 hϑ _, ?_, ?_⟩
  · refine le_iInf₂ fun a ha => le_iInf₂ fun b hb => ENNReal.ofReal_le_ofReal ?_
    have ha' : euclidNormVec (a - collinearCentres c₁ u d i) ≤ d / 16 :=
      tsupport_shifted_bump_subset hd _ ha
    have hb' : euclidNormVec (b - collinearCentres c₁ u d j) ≤ d / 16 :=
      tsupport_shifted_bump_subset hd _ hb
    have h1 := abs_euclidNormVec_sub_le
      (collinearCentres c₁ u d i - collinearCentres c₁ u d j) (a - b)
    have h2 : (collinearCentres c₁ u d i - collinearCentres c₁ u d j) - (a - b) =
        (b - collinearCentres c₁ u d j) - (a - collinearCentres c₁ u d i) := by abel
    have h3 := euclidNormVec_sub_le (b - collinearCentres c₁ u d j)
      (a - collinearCentres c₁ u d i)
    rw [h2] at h1
    have h4 := (dist_collinearCentres (c₁ := c₁) hd hu hij).1
    have h5 := (abs_le.1 h1).2
    linarith
  · refine iInf₂_le_of_le _ (mem_tsupport_shifted_bump d _)
      (iInf₂_le_of_le _ (mem_tsupport_shifted_bump d _) ?_)
    exact ENNReal.ofReal_le_ofReal (dist_collinearCentres hd hu hij).2
theorem collinearR4HasTranslates_holds {d ϑ : ℝ} (hds : IsScaleShape d ϑ)
    (hϑ : ϑ ≤ collinearThetaBound) : CollinearR4HasTranslates d ϑ := by
  intro c₁ u hu
  refine ⟨radialBump d, collinearCentres c₁ u d, by simp [collinearCentres],
    fun i _ => ⟨2 * ((i : ℕ) : ℝ) * d, ?_⟩, fun x hx => radialBump_eq_zero hds.1 ?_,
    fun i => ?_, translateFamily_mem hds hϑ c₁ u hu⟩
  · simp [collinearCentres]
  · have : d / 16 < euclidNormVec (x - 0) := not_le.1 hx
    rw [sub_zero] at this
    exact this.le
  · exact (contDiff_radialBump d).comp (contDiff_id.sub contDiff_const)
theorem uniformNorm_nonneg {X : Type*} (f : X → ℝ) : 0 ≤ uniformNorm f :=
  Real.iSup_nonneg fun _ => norm_nonneg _
theorem abs_le_uniformNorm {X : Type*} {f : X → ℝ} (hb : IsBoundedFun f) (x : X) :
    |f x| ≤ uniformNorm f := by
  obtain ⟨C, hC⟩ := hb
  refine le_ciSup (f := fun x => ‖f x‖) ⟨C, ?_⟩ x
  rintro _ ⟨y, rfl⟩
  exact hC y
theorem integralR4_le {f : (Fin 4 → ℝ) → ℝ} {x : Fin 4 → ℝ} {r : ℝ} (hr : 0 < r)
    (hb : IsBoundedFun f) (hv : ∀ t, t ∉ closedBallR4 x r → f t = 0) :
    integralR4 f ≤ omega4 * r ^ 4 * uniformNorm f := by
  have hω : 0 ≤ omega4 * r ^ 4 := by
    unfold omega4
    positivity
  have hM := uniformNorm_nonneg f
  by_cases hi : Integrable f
  · have hm : MeasurableSet (closedBallR4 x r) := (isClosed_closedBallR4 x r).measurableSet
    have hfin : volume (closedBallR4 x r) ≠ ⊤ := by
      rw [volume_closedBallR4 x hr]
      exact ENNReal.ofReal_ne_top
    have hI : Integrable ((closedBallR4 x r).indicator fun _ => uniformNorm f) :=
      (integrable_indicator_iff hm).2 (integrableOn_const hfin)
    have h1 : ∫ t, f t ≤ ∫ t, (closedBallR4 x r).indicator (fun _ => uniformNorm f) t := by
      refine integral_mono hi hI fun t => ?_
      by_cases ht : t ∈ closedBallR4 x r
      · simp only [indicator_of_mem ht]
        exact (le_abs_self _).trans (abs_le_uniformNorm hb t)
      · simp only [indicator_of_notMem ht, hv t ht, le_refl]
    rw [integral_indicator_const _ hm, Measure.real, volume_closedBallR4 x hr,
      ENNReal.toReal_ofReal hω, smul_eq_mul] at h1
    exact h1
  · rw [integralR4, integral_undef hi]
    positivity
theorem integralBoundR4_holds {d : ℝ} (hd : 0 < d) : IntegralBoundR4 d := by
  intro f x hb _ hv
  have h := integralR4_le (by positivity : 0 < d / 16) hb hv
  exact h
theorem isBoundedFun_of_lipschitz {g : (Fin 4 → ℝ) → ℝ} {c : Fin 4 → ℝ} {r : ℝ}
    (hg : IsLipschitzFor euclidDistR4 g) (hs : euclideanTSupport g ⊆ closedBallR4 c r) :
    IsBoundedFun g := by
  obtain ⟨C, hC, hl⟩ := hg
  refine ⟨|g c| + C * |r|, fun t => ?_⟩
  by_cases ht : t ∈ closedBallR4 c r
  · have h1 := hl t c
    have h2 : euclidDistR4 t c ≤ r := ht
    have h3 := mul_le_mul_of_nonneg_left (h2.trans (le_abs_self r)) hC
    have h4 : ‖g t‖ ≤ ‖g t - g c‖ + ‖g c‖ := by
      have := norm_add_le (g t - g c) (g c)
      simpa using this
    rw [Real.norm_eq_abs (g c)] at h4
    linarith
  · have h0 : g t = 0 := image_eq_zero_of_notMem_tsupport fun hm => ht (hs hm)
    rw [h0, norm_zero]
    positivity
theorem collinearQuadsR4_eq_empty {d ϑ : ℝ} (hds : IsScaleShape d ϑ)
    (hlt : omega4 * (16 : ℝ) ^ (-4 : ℤ) < ϑ) : collinearQuadsR4 d ϑ = ∅ := by
  have hd := hds.1
  refine eq_empty_iff_forall_notMem.2 ?_
  rintro g ⟨hg, c, -, hc⟩
  obtain ⟨x₁, x₂, ⟨hlip, -, ⟨y, hy⟩, -, hint, -⟩, -⟩ := hg.2.2 0 1 (by decide)
  have hb : IsBoundedFun (g 0) := isBoundedFun_of_lipschitz hlip (hc 0)
  have hv : ∀ t, t ∉ closedBallR4 (c 0) (d / 16) → g 0 t = 0 := fun t ht =>
    image_eq_zero_of_notMem_tsupport fun hm => ht (hc 0 hm)
  have h1 := integralR4_le (by positivity : 0 < d / 16) hb hv
  have hM : 0 < uniformNorm (g 0) := lt_of_lt_of_le (abs_pos.2 hy) (abs_le_uniformNorm hb y)
  have h3 : (16 : ℝ) ^ (-4 : ℤ) = 1 / 16 ^ 4 := by norm_num
  rw [h3] at hlt
  have hp : 0 < uniformNorm (g 0) * d ^ 4 := by positivity
  have h4 := mul_lt_mul_of_pos_right hlt hp
  have h5 : omega4 * (1 / 16 ^ 4) * (uniformNorm (g 0) * d ^ 4) =
      omega4 * (d / 16) ^ 4 * uniformNorm (g 0) := by ring
  rw [h5] at h4
  nlinarith
theorem integralBoundTorus_holds
    (hCells : TorusMeasure.TranslatedLatticeCells.CellsAndBallsStatement)
    (hMeasure : TorusCovering.CoveringIntegralVolumeStatement)
    (s : Conventions.StandingParameters) {d : ℝ}
    (hd : 0 < d) (h40 : 40 * d ≤ PeriodicLattice.torusSide s.L s.m) :
    IntegralBoundTorus s d := by
  intro f x hb hm hv
  have hr : 0 < d / 16 := by positivity
  obtain ⟨-, -, -, hmeas, hvol, hball⟩ := (hCells s).2.1 x (d / 16) hr
  have hball' := hball (by linarith)
  set B := closedWrapBall x (d / 16) with hB
  have hind : TorusCovering.IsBddMeasurable (B.indicator (1 : s.Torus → ℝ)) := by
    refine ⟨⟨1, fun w => ?_⟩, (isMeasurableTorusSet_iff_indicator B).1 hmeas⟩
    by_cases hw : w ∈ B <;> simp [hw]
  have hM := uniformNorm_nonneg f
  have hfacts := (hMeasure s).2.1 _ _ hind hind (uniformNorm f) 0
  have hmono := ((hMeasure s).2.1 f _ ⟨hb, hm⟩ hfacts.1 0 0).2.2.2 (fun w => ?_)
  · rw [hfacts.2.2.1] at hmono
    have hv2 : uniformNorm f * torusIntegral (B.indicator (1 : s.Torus → ℝ)) ≤
        uniformNorm f * (omega4 * (d / 16) ^ 4) := mul_le_mul_of_nonneg_left hvol hM
    linarith
  · by_cases hw : w ∈ B
    · simp only [indicator_of_mem hw, Pi.one_apply, mul_one, add_zero]
      exact (le_abs_self _).trans (abs_le_uniformNorm hb w)
    · have hw' : w ∉ closedBallTorus (ℓ := PeriodicLattice.torusSide s.L s.m) x (d / 16) := by
        rw [← hball']
        exact hw
      simp only [indicator_of_notMem hw, hv w hw', mul_zero, add_zero, le_refl]
theorem isLift_proj (hMeasure : TorusCovering.CoveringIntegralVolumeStatement)
    (s : Conventions.StandingParameters) (c : Fin 4 → ℝ) : IsLift s (proj s c) c :=
  (((hMeasure s).1.2.2.2.1) _ _).2 rfl
theorem mem_quadsR4_of_isBallLift (hMeasure : TorusCovering.CoveringIntegralVolumeStatement)
    (hT : QuadrupleGeometry.GeometryOnTorus) {s : Conventions.StandingParameters} {d ϑ : ℝ}
    {f : Fin 4 → s.Torus → ℝ} {g : Fin 4 → (Fin 4 → ℝ) → ℝ} (hl : IsBallLift s d ϑ f g) :
    g ∈ quadsR4 d ϑ := by
  obtain ⟨hf, c, hsupp, hg⟩ := hl
  obtain ⟨-, -, hBalls, hLifts, -⟩ := hT s d ϑ hf.1.1 hf.1.2 hf.2.1 f hf
  have himg := hBalls.2 (proj s c) c (isLift_proj hMeasure s c)
  have hmem := (hLifts (proj s c) c (fun i => himg ▸ hsupp i) himg).2.1
  have : g = fun i => QuadrupleGeometry.liftOverBall c d (f i) := funext hg
  rw [this]
  exact hmem
theorem mem_tsupport_of_shift {a b : (Fin 4 → ℝ) → ℝ} {p : Fin 4 → ℝ}
    (h : ∀ t, b (t + p) = a t) {w : Fin 4 → ℝ} (hw : w ∈ tsupport b) : w - p ∈ tsupport a := by
  have hab : a = b ∘ (Homeomorph.addRight p) := funext fun t => (h t).symm
  rw [hab, tsupport_comp_eq_preimage]
  simpa using hw
theorem ballLiftsAgree_holds (hMeasure : TorusCovering.CoveringIntegralVolumeStatement)
    (hT : QuadrupleGeometry.GeometryOnTorus) (s : Conventions.StandingParameters) (d ϑ : ℝ) :
    BallLiftsAgree s d ϑ := by
  intro f hf g g' hl hl'
  have hq' := mem_quadsR4_of_isBallLift hMeasure hT hl'
  obtain ⟨-, c, hsupp, hg⟩ := hl
  obtain ⟨-, c', hsupp', hg'⟩ := hl'
  obtain ⟨-, -, -, -, hP⟩ := hT s d ϑ hf.1.1 hf.1.2 hf.2.1 f hf
  obtain ⟨k, hk⟩ := hP c c' hsupp hsupp'
  set p := latticeTranslate (PeriodicLattice.torusSide s.L s.m) k with hp
  have hshift : ∀ i t, g' i (t + p) = g i t := by
    intro i t
    rw [hg, hg']
    exact hk t i
  refine ⟨?_, ?_⟩
  · rintro u ⟨hu, hs⟩
    refine ⟨hu, fun i j hij x hx y hy => ?_⟩
    have := hs i j hij (x - p) (mem_tsupport_of_shift (hshift i) hx) (y - p)
      (mem_tsupport_of_shift (hshift j) hy)
    rwa [sub_sub_sub_cancel_right] at this
  · rintro ⟨-, b, ⟨u, hu, hline⟩, hb⟩
    refine ⟨hq', fun i => b i + p, ⟨u, hu, fun i j => ?_⟩, fun i x hx => ?_⟩
    · rw [add_sub_add_right_eq_sub]
      exact hline i j
    · have h1 : euclidNormVec (x - p - b i) ≤ d / 16 :=
        hb i (mem_tsupport_of_shift (hshift i) hx)
      have h2 : x - p - b i = x - (b i + p) := by abel
      rw [h2] at h1
      exact h1
theorem isBallLift_periodizedQuad
    (hBall : TorusMeasure.BallProjection.BallProjectionStatement)
    (hR4 : QuadrupleGeometry.GeometryOnR4) {s : Conventions.StandingParameters} {d ϑ : ℝ}
    (hds : IsScaleShape d ϑ) (h40 : 40 * d ≤ PeriodicLattice.torusSide s.L s.m)
    {g : Fin 4 → (Fin 4 → ℝ) → ℝ} (hg : g ∈ quadsR4 d ϑ) :
    IsBallLift s d ϑ (periodizedQuad s g) g := by
  have hd := hds.1
  obtain ⟨-, ⟨-, ⟨c, hc⟩, -⟩, hTr⟩ := hR4 d ϑ hd hds.2 g hg
  refine ⟨(hTr s h40).2, c, ?_⟩
  have key : ∀ i, torusTSupport (periodizedQuad s g i) ⊆
        proj s '' closedBallR4 c (9 * d) ∧
      g i = ballLift s d c (periodizedQuad s g i) := by
    intro i
    obtain ⟨-, -, hCorr, hAll⟩ := hBall s (9 * d) c (by positivity) (by linarith)
    have hvan : ∀ t, t ∉ closedBallR4 c (9 * d) → g i t = 0 := fun t ht =>
      image_eq_zero_of_notMem_tsupport fun hm => ht (hc i hm)
    obtain ⟨b, hb, -⟩ := hCorr.1 (g i) hvan
    obtain ⟨hTb, -, -, hS, -⟩ := hAll (g i) b hb
    have hbt : periodizedQuad s g i = b := hTb.2.2.2.symm
    rw [hbt]
    refine ⟨?_, ?_⟩
    · rw [hS.2.2]
      exact image_mono hS.1
    · funext t
      by_cases ht : t ∈ closedBallR4 c (9 * d)
      · simp only [ballLift, indicator_of_mem ht, Function.comp]
        exact (hb.2.1 t ht).symm
      · simp only [ballLift, indicator_of_notMem ht]
        exact hvan t ht
  exact ⟨fun i => (key i).1, fun i => (key i).2⟩
theorem periodizationAgrees_holds
    (hBall : TorusMeasure.BallProjection.BallProjectionStatement)
    (hMeasure : TorusCovering.CoveringIntegralVolumeStatement)
    (hR4 : QuadrupleGeometry.GeometryOnR4)
    (hT : QuadrupleGeometry.GeometryOnTorus) {s : Conventions.StandingParameters} {d ϑ : ℝ}
    (hds : IsScaleShape d ϑ) (h40 : 40 * d ≤ PeriodicLattice.torusSide s.L s.m) :
    PeriodizationAgrees s d ϑ := by
  intro g hg
  have hl := isBallLift_periodizedQuad hBall hR4 hds h40 hg
  have hq := hl.1
  refine ⟨hl, ⟨?_, ?_⟩, ⟨?_, ?_⟩⟩
  · rintro ⟨-, g', hl', -, u, hu⟩
    exact ⟨hg, hg, u, (ballLiftsAgree_holds hMeasure hT s d ϑ _ hq g' g hl' hl).1 u hu⟩
  · rintro ⟨-, hs⟩
    exact ⟨hq, g, hl, hs⟩
  · rintro ⟨-, g', hl', hg'⟩
    exact (ballLiftsAgree_holds hMeasure hT s d ϑ _ hq g' g hl' hl).2 hg'
  · intro hc
    exact ⟨hq, g, hl, hc⟩
theorem euclidNormVec_basis_zero : euclidNormVec (Pi.single 0 1 : Fin 4 → ℝ) = 1 := by
  simp [euclidNormVec, Pi.single_apply]
theorem collinearQuadruplesStatement_holds
    (hBall : TorusMeasure.BallProjection.BallProjectionStatement)
    (hCells : TorusMeasure.TranslatedLatticeCells.CellsAndBallsStatement)
    (hMeasure : TorusCovering.CoveringIntegralVolumeStatement)
    (hGeom : QuadrupleGeometry.QuadrupleGeometryStatement) : CollinearQuadruplesStatement := by
  obtain ⟨hR4, hT⟩ := hGeom
  refine ⟨⟨collinearThetaBound_pos, collinearThetaBound_le_one⟩, ?_, fun d ϑ hds => ?_⟩
  · rw [volumeR4, volume_closedBallR4 0 (by norm_num)]
    congr 2
    norm_num
  have hd := hds.1
  refine ⟨isShapeAxis_of_geometry hR4 hds, nestedClassesR4_holds hR4 hds,
    collinearR4HasTranslates_holds hds, integralBoundR4_holds hd, collinearQuadsR4_eq_empty hds,
    fun s h40 => ?_⟩
  refine ⟨⟨?_, fun f hf => hf.1⟩, integralBoundTorus_holds hCells hMeasure s hd h40, ?_,
    ballLiftsAgree_holds hMeasure hT s d ϑ, periodizationAgrees_holds hBall hMeasure hR4 hT hds h40,
    ?_⟩
  · rintro f ⟨hf, g, hl, hg⟩
    exact ⟨hf, g, hl, ((nestedClassesR4_holds hR4 hds).1 hg).2⟩
  · intro hlt
    refine eq_empty_iff_forall_notMem.2 ?_
    rintro f ⟨-, g, -, hg⟩
    rw [collinearQuadsR4_eq_empty hds hlt] at hg
    exact hg
  · intro hϑ
    have hg := translateFamily_mem hds hϑ 0 (Pi.single 0 1) euclidNormVec_basis_zero
    have hl := isBallLift_periodizedQuad (s := s) hBall hR4 hds h40 hg.1
    exact ⟨_, hl.1, _, hl, hg⟩
end QuadrupleClasses.Collinear
end YangMills.Construction
