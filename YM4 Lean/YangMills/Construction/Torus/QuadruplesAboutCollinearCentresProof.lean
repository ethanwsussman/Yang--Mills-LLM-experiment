import YangMills.Construction.Continuum.RegularityAndSupportsOfTheUnitKernelsProof
import YangMills.Construction.Torus.CollinearQuadruplesProof
import YangMills.Construction.Torus.QuadruplesAboutCollinearCentres
import Mathlib
set_option autoImplicit false
open MeasureTheory Set Filter
noncomputable section
namespace YangMills.Construction
open TorusMetric TestFunctions TorusMeasure PlaquetteSupports
namespace QuadrupleClasses.CollinearCentres
open Collinear
theorem euclidNormVec_eq_norm (v : Fin 4 → ℝ) :
    euclidNormVec v = ‖(WithLp.toLp 2 v : EuclideanSpace ℝ (Fin 4))‖ := by apply _root_.YangMills.Construction.AmbientPoints.euclidNormVec_eq_norm <;> assumption
theorem euclidNormVec_nonneg (v : Fin 4 → ℝ) : 0 ≤ euclidNormVec v := Real.sqrt_nonneg _
theorem euclidNormVec_sub_le (a b : Fin 4 → ℝ) :
    euclidNormVec (a - b) ≤ euclidNormVec a + euclidNormVec b := by apply _root_.YangMills.Construction.QuadrupleClasses.Collinear.euclidNormVec_sub_le <;> assumption
theorem euclidNormVec_smul (t : ℝ) (a : Fin 4 → ℝ) :
    euclidNormVec (t • a) = |t| * euclidNormVec a := by apply _root_.YangMills.SharedProofs.p37834 <;> assumption
theorem euclidNormVec_sq (v : Fin 4 → ℝ) : euclidNormVec v ^ 2 = ∑ μ, v μ ^ 2 := by apply _root_.YangMills.Construction.Parametrix.UnitKernelSupport.euclidNormVec_sq <;> assumption
theorem abs_euclidNormVec_sub_le (a b : Fin 4 → ℝ) :
    |euclidNormVec a - euclidNormVec b| ≤ euclidNormVec (a - b) := by apply _root_.YangMills.Construction.QuadrupleClasses.Collinear.abs_euclidNormVec_sub_le <;> assumption
theorem isClosed_closedBallR4 (x : Fin 4 → ℝ) (r : ℝ) : IsClosed (closedBallR4 x r) := by apply _root_.YangMills.Construction.TestPairs.isClosed_closedBallR4 <;> assumption
def quarticProfile (ρ : ℝ) : ℝ := max (1 - ρ ^ 2) 0 ^ 2
def radialBump (d : ℝ) (x : Fin 4 → ℝ) : ℝ := quarticProfile (16 / d * euclidNormVec x)
theorem quarticProfile_nonneg (ρ : ℝ) : 0 ≤ quarticProfile ρ := sq_nonneg _
theorem quarticProfile_le_one (ρ : ℝ) : quarticProfile ρ ≤ 1 := by apply _root_.YangMills.Construction.QuadrupleClasses.Collinear.bumpProfile_le_one <;> assumption
theorem quarticProfile_of_sq_le_one {ρ : ℝ} (h : ρ ^ 2 ≤ 1) :
    quarticProfile ρ = (1 - ρ ^ 2) ^ 2 := by apply _root_.YangMills.Construction.QuadrupleClasses.Collinear.bumpProfile_of_sq_le_one <;> assumption
theorem quarticProfile_of_one_le_sq {ρ : ℝ} (h : 1 ≤ ρ ^ 2) : quarticProfile ρ = 0 := by apply _root_.YangMills.Construction.QuadrupleClasses.Collinear.bumpProfile_of_one_le_sq <;> assumption
theorem abs_quarticProfile_sub_le {ρ ρ' : ℝ} (h0 : 0 ≤ ρ) (h0' : 0 ≤ ρ') :
    |quarticProfile ρ - quarticProfile ρ'| ≤ 2 * |ρ - ρ'| := by apply _root_.YangMills.Construction.QuadrupleClasses.Collinear.abs_bumpProfile_sub_le <;> assumption
theorem radialBump_nonneg (d : ℝ) (x : Fin 4 → ℝ) : 0 ≤ radialBump d x := quarticProfile_nonneg _
theorem radialBump_le_one (d : ℝ) (x : Fin 4 → ℝ) : radialBump d x ≤ 1 := quarticProfile_le_one _
theorem radialBump_zero (d : ℝ) : radialBump d 0 = 1 := by
  have : euclidNormVec 0 = 0 := by simp [euclidNormVec]
  simp [radialBump, this, quarticProfile]
theorem radialBump_eq_zero {d : ℝ} (hd : 0 < d) {x : Fin 4 → ℝ} (hx : d / 16 ≤ euclidNormVec x) :
    radialBump d x = 0 := by
  apply quarticProfile_of_one_le_sq
  have h1 : 1 ≤ 16 / d * euclidNormVec x := by
    rw [div_mul_eq_mul_div, le_div_iff₀ hd]
    linarith
  nlinarith
theorem radialBump_lipschitz {d : ℝ} (hd : 0 < d) (x y : Fin 4 → ℝ) :
    |radialBump d x - radialBump d y| ≤ 32 / d * euclidNormVec (x - y) := by
  have hκ : 0 ≤ 16 / d := by positivity
  have h1 := abs_quarticProfile_sub_le (mul_nonneg hκ (euclidNormVec_nonneg x))
    (mul_nonneg hκ (euclidNormVec_nonneg y))
  have h2 := abs_euclidNormVec_sub_le x y
  have h3 : |16 / d * euclidNormVec x - 16 / d * euclidNormVec y| =
      16 / d * |euclidNormVec x - euclidNormVec y| := by
    rw [← mul_sub, abs_mul, abs_of_nonneg hκ]
  have h4 := mul_le_mul_of_nonneg_left h2 hκ
  have h5 : 32 / d = 2 * (16 / d) := by ring
  unfold radialBump
  rw [h3] at h1
  rw [h5]
  nlinarith
theorem contDiff_sq_max_zero : ContDiff ℝ 1 (fun σ : ℝ => max σ 0 ^ 2) := by apply _root_.YangMills.Construction.QuadrupleClasses.Collinear.contDiff_sq_max_zero <;> assumption
theorem contDiff_radialBump (d : ℝ) : ContDiff ℝ 1 (radialBump d) := by
  have h : radialBump d = (fun σ : ℝ => max σ 0 ^ 2) ∘
      fun x : Fin 4 → ℝ => 1 - (16 / d) ^ 2 * ∑ μ, x μ ^ 2 := by
    funext x
    simp only [radialBump, quarticProfile, Function.comp, mul_pow, euclidNormVec_sq]
  rw [h]
  refine contDiff_sq_max_zero.comp ?_
  fun_prop
theorem integral_Ioi_radial {d : ℝ} (hd : 0 < d) :
    ∫ y in Ioi (0 : ℝ), y ^ 3 • quarticProfile (16 / d * y) = (d / 16) ^ 4 / 24 := by apply _root_.YangMills.Construction.QuadrupleClasses.Collinear.integral_Ioi_radial_profile <;> assumption
theorem integral_radialBump {d : ℝ} (hd : 0 < d) :
    ∫ x, radialBump d x = omega4 * (d / 16) ^ 4 / 6 := by
  have h1 := (EuclideanSpace.volume_preserving_symm_measurableEquiv_toLp (Fin 4)).integral_comp'
    (radialBump d)
  rw [← h1]
  have h2 : ∀ y : EuclideanSpace ℝ (Fin 4),
      radialBump d ((MeasurableEquiv.toLp 2 (Fin 4 → ℝ)).symm y) =
        (fun ρ => quarticProfile (16 / d * ρ)) ‖y‖ := by
    intro y
    simp only [radialBump, euclidNormVec_eq_norm]
    rfl
  simp_rw [h2]
  rw [integral_fun_norm_addHaar (volume : Measure (EuclideanSpace ℝ (Fin 4)))
    (fun ρ => quarticProfile (16 / d * ρ))]
  have hf : Module.finrank ℝ (EuclideanSpace ℝ (Fin 4)) = 4 := by simp
  have hv : (volume : Measure (EuclideanSpace ℝ (Fin 4))).real (Metric.ball 0 1) = omega4 := by
    rw [Measure.real, InnerProductSpace.volume_ball_of_dim_even (k := 2) (by simp)]
    simp [omega4, Nat.factorial]
    positivity
  rw [hf, hv]
  simp only [show 4 - 1 = 3 from rfl]
  rw [integral_Ioi_radial hd]
  simp only [nsmul_eq_mul, smul_eq_mul]
  push_cast
  ring
theorem collinearThetaBound_pos : 0 < collinearThetaBound := by apply _root_.YangMills.Construction.QuadrupleClasses.Collinear.collinearThetaBound_pos <;> assumption
theorem collinearThetaBound_lt : collinearThetaBound < 1 / 32 := by apply _root_.YangMills.Construction.QuadrupleClasses.Collinear.collinearThetaBound_lt <;> assumption
theorem uniformNorm_translate_radialBump (d : ℝ) (c : Fin 4 → ℝ) :
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
theorem tsupport_translate_radialBump_subset {d : ℝ} (hd : 0 < d) (c : Fin 4 → ℝ) :
    tsupport (fun x => radialBump d (x - c)) ⊆ closedBallR4 c (d / 16) := by
  refine closure_minimal ?_ (isClosed_closedBallR4 _ _)
  intro x hx
  by_contra hc
  exact hx (radialBump_eq_zero hd (le_of_lt (not_le.1 hc)))
theorem isLipschitzFor_translate_radialBump {d : ℝ} (hd : 0 < d) (c : Fin 4 → ℝ) :
    IsLipschitzFor euclidDistR4 (fun x => radialBump d (x - c)) := by
  refine ⟨32 / d, by positivity, fun x y => ?_⟩
  have h := radialBump_lipschitz hd (x - c) (y - c)
  rw [sub_sub_sub_cancel_right] at h
  exact h
theorem isShapedBump_translate_radialBump {d ϑ : ℝ} (hd : 0 < d) (hϑ0 : 0 < ϑ)
    (hϑ : ϑ ≤ collinearThetaBound) (c : Fin 4 → ℝ) :
    IsShapedBump euclidDistR4 closedBallR4 integralR4 d ϑ c
      (fun x => radialBump d (x - c)) := by
  have hsub : closedBallR4 c (d / 16) ⊆ closedBallR4 c d := by
    intro y hy
    have h1 : euclidNormVec (y - c) ≤ d / 16 := hy
    show euclidNormVec (y - c) ≤ d
    linarith
  refine ⟨isLipschitzFor_translate_radialBump hd c, fun y => radialBump_nonneg _ _,
    ⟨c, by simp [radialBump_zero]⟩, (tsupport_translate_radialBump_subset hd c).trans hsub, ?_, ?_⟩
  · rw [uniformNorm_translate_radialBump, integralR4,
      integral_sub_right_eq_self (fun x => radialBump d x) c, integral_radialBump hd]
    have h := mul_le_mul_of_nonneg_right hϑ (by positivity : 0 ≤ d ^ 4)
    have h2 : collinearThetaBound * d ^ 4 = omega4 * (d / 16) ^ 4 / 6 := by
      unfold collinearThetaBound
      ring
    rw [mul_one, ← h2]
    exact h
  · rw [uniformNorm_translate_radialBump]
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
theorem rescaledBump_eq_radialBump {d : ℝ} (hd : 0 < d) : rescaledBump d = radialBump d := by
  funext x
  have hκ : 0 ≤ 16 / d := by positivity
  have hn : euclidNormVec ((16 / d) • x) = 16 / d * euclidNormVec x := by
    rw [euclidNormVec_smul, abs_of_nonneg hκ]
  have h0 : 0 ≤ 16 / d * euclidNormVec x := mul_nonneg hκ (euclidNormVec_nonneg x)
  unfold rescaledBump radialBump radialBumpR4
  rw [hn]
  split_ifs with h
  · rw [quarticProfile_of_sq_le_one (by nlinarith)]
  · rw [quarticProfile_of_one_le_sq (by nlinarith [not_le.1 h])]
theorem bumpsCentredAt_eq {d : ℝ} (hd : 0 < d) (c : Fin 4 → Fin 4 → ℝ) :
    bumpsCentredAt d c = translateFamily (radialBump d) c := by
  unfold bumpsCentredAt
  rw [rescaledBump_eq_radialBump hd]
theorem radialBump_ne_zero {d : ℝ} (hd : 0 < d) {x : Fin 4 → ℝ} (hx : euclidNormVec x < d / 16) :
    radialBump d x ≠ 0 := by
  have hκ : 0 ≤ 16 / d := by positivity
  have h0 : 0 ≤ 16 / d * euclidNormVec x := mul_nonneg hκ (euclidNormVec_nonneg x)
  have h1 : 16 / d * euclidNormVec x < 1 := by
    rw [div_mul_eq_mul_div, div_lt_one hd]
    linarith
  have h2 : (16 / d * euclidNormVec x) ^ 2 < 1 := by nlinarith
  unfold radialBump
  rw [quarticProfile_of_sq_le_one h2.le]
  exact pow_ne_zero 2 (ne_of_gt (by linarith))
theorem closedBallR4_subset_tsupport {d : ℝ} (hd : 0 < d) (c : Fin 4 → ℝ) :
    closedBallR4 c (d / 16) ⊆ tsupport (fun x => radialBump d (x - c)) := by
  intro x hx
  have hx' : euclidNormVec (x - c) ≤ d / 16 := hx
  have hr : 0 < d / 16 := by positivity
  have hcont : Continuous (fun τ : ℝ => c + τ • (x - c)) := by fun_prop
  have hlim : Tendsto (fun τ : ℝ => c + τ • (x - c)) (nhdsWithin 1 (Iio 1)) (nhds x) := by
    have h := (hcont.tendsto 1).mono_left (nhdsWithin_le_nhds (s := Iio 1))
    simpa using h
  refine mem_closure_of_tendsto hlim ?_
  filter_upwards [Ioo_mem_nhdsLT (show (0 : ℝ) < 1 by norm_num)] with τ hτ
  show radialBump d (c + τ • (x - c) - c) ≠ 0
  apply radialBump_ne_zero hd
  rw [add_sub_cancel_left, euclidNormVec_smul, abs_of_pos hτ.1]
  have h1 := mul_le_mul_of_nonneg_left hx' hτ.1.le
  have h2 := mul_pos (sub_pos.2 hτ.2) hr
  nlinarith
theorem euclideanTSupport_rescaledBump {d : ℝ} (hd : 0 < d) :
    euclideanTSupport (rescaledBump d) = closedBallR4 0 (d / 16) := by
  rw [rescaledBump_eq_radialBump hd]
  have h : radialBump d = fun x => radialBump d (x - 0) := by
    funext x
    rw [sub_zero]
  rw [h]
  exact (tsupport_translate_radialBump_subset hd 0).antisymm (closedBallR4_subset_tsupport hd 0)
theorem collinearThetaBound_eq : collinearThetaBound = Real.pi ^ 2 / (12 * 16 ^ 4) := by
  unfold collinearThetaBound omega4
  ring
theorem collinearThetaBound_lt_zpow : collinearThetaBound < (16 : ℝ) ^ (-4 : ℤ) := by
  have h := Real.pi_lt_d2
  have h0 := Real.pi_pos
  have h3 : (16 : ℝ) ^ (-4 : ℤ) = 1 / 16 ^ 4 := by norm_num
  rw [collinearThetaBound_eq, h3, div_lt_div_iff₀ (by norm_num) (by norm_num)]
  nlinarith
theorem equallySpacedPoints_sub (y e : Fin 4 → ℝ) (t d : ℝ) (i j : Fin 4) :
    equallySpacedPoints y e t d i - equallySpacedPoints y e t d j =
      ((((i : ℕ) : ℝ) - ((j : ℕ) : ℝ)) * t * d) • e := by
  funext μ
  simp only [equallySpacedPoints, Pi.sub_apply, Pi.add_apply, Pi.smul_apply, smul_eq_mul]
  ring
theorem abs_index_sub_le_three (i j : Fin 4) : |((i : ℕ) : ℝ) - ((j : ℕ) : ℝ)| ≤ 3 := by
  have hi : ((i : ℕ) : ℝ) ≤ 3 := by exact_mod_cast (by omega : (i : ℕ) ≤ 3)
  have hj : ((j : ℕ) : ℝ) ≤ 3 := by exact_mod_cast (by omega : (j : ℕ) ≤ 3)
  rw [abs_le]
  constructor <;> linarith
theorem one_le_abs_index_sub {i j : Fin 4} (h : i ≠ j) :
    1 ≤ |((i : ℕ) : ℝ) - ((j : ℕ) : ℝ)| := by
  have hne : (i : ℕ) ≠ j := fun e => h (Fin.ext e)
  rcases Nat.lt_or_gt_of_ne hne with hlt | hlt
  · have h1 : ((i : ℕ) : ℝ) + 1 ≤ ((j : ℕ) : ℝ) := by exact_mod_cast hlt
    rw [abs_sub_comm, abs_of_nonneg (by linarith)]
    linarith
  · have h1 : ((j : ℕ) : ℝ) + 1 ≤ ((i : ℕ) : ℝ) := by exact_mod_cast hlt
    rw [abs_of_nonneg (by linarith)]
    linarith
theorem euclidNormVec_equallySpacedPoints_sub {y e : Fin 4 → ℝ} {t d : ℝ} (hd : 0 < d)
    (he : euclidNormVec e = 1) (ht : SpacingCondition t) (i j : Fin 4) :
    euclidNormVec (equallySpacedPoints y e t d i - equallySpacedPoints y e t d j) =
      |((i : ℕ) : ℝ) - ((j : ℕ) : ℝ)| * t * d := by
  have ht0 : 0 < t := by linarith [ht.1]
  rw [equallySpacedPoints_sub, euclidNormVec_smul, he, mul_one, abs_mul, abs_mul, abs_of_pos hd,
    abs_of_pos ht0]
theorem exists_close_points {y e : Fin 4 → ℝ} {t d : ℝ} (hd : 0 < d) (he : euclidNormVec e = 1)
    (ht : SpacingCondition t) {i j : Fin 4} (hij : i ≠ j) :
    ∃ u ∈ closedBallR4 (equallySpacedPoints y e t d i) (d / 16),
      ∃ v ∈ closedBallR4 (equallySpacedPoints y e t d j) (d / 16),
        euclidNormVec (u - v) ≤ 6 * d := by
  set a : ℝ := ((i : ℕ) : ℝ) - ((j : ℕ) : ℝ) with ha
  have h1 : 1 ≤ |a| := one_le_abs_index_sub hij
  have h3 : |a| ≤ 3 := abs_index_sub_le_three i j
  have ht1 := ht.1
  have ht2 := ht.2
  have hat : |a| * t ≤ 49 / 8 := by nlinarith [abs_nonneg a]
  have hat1 : 0 ≤ |a| * t := mul_nonneg (abs_nonneg a) (by linarith)
  obtain ⟨σ, hσ, hb⟩ : ∃ σ : ℝ, |σ| = 1 ∧ |a * t + σ / 8| ≤ 6 := by
    rcases le_total 0 a with h0 | h0
    · rw [abs_of_nonneg h0] at hat hat1
      refine ⟨-1, by norm_num, ?_⟩
      rw [abs_le]
      constructor <;> linarith
    · rw [abs_of_nonpos h0] at hat hat1
      refine ⟨1, by norm_num, ?_⟩
      rw [abs_le]
      constructor <;> linarith
  have hr : 0 ≤ d / 16 := by positivity
  have hstep : euclidNormVec ((σ * (d / 16)) • e) = d / 16 := by
    rw [euclidNormVec_smul, he, abs_mul, hσ, abs_of_nonneg hr]
    ring
  refine ⟨equallySpacedPoints y e t d i + (σ * (d / 16)) • e, ?_,
    equallySpacedPoints y e t d j - (σ * (d / 16)) • e, ?_, ?_⟩
  · show euclidNormVec (equallySpacedPoints y e t d i + (σ * (d / 16)) • e -
      equallySpacedPoints y e t d i) ≤ _
    rw [add_sub_cancel_left, hstep]
  · show euclidNormVec (equallySpacedPoints y e t d j - (σ * (d / 16)) • e -
      equallySpacedPoints y e t d j) ≤ _
    have hneg : equallySpacedPoints y e t d j - (σ * (d / 16)) • e -
        equallySpacedPoints y e t d j = (-(σ * (d / 16))) • e := by
      rw [sub_sub_cancel_left, neg_smul]
    rw [hneg, euclidNormVec_smul, he, abs_neg, abs_mul, hσ, abs_of_nonneg hr]
    linarith
  · have heq : (equallySpacedPoints y e t d i + (σ * (d / 16)) • e) -
        (equallySpacedPoints y e t d j - (σ * (d / 16)) • e) = ((a * t + σ / 8) * d) • e := by
      funext μ
      simp only [equallySpacedPoints, ha, Pi.sub_apply, Pi.add_apply, Pi.smul_apply, smul_eq_mul]
      ring
    rw [heq, euclidNormVec_smul, he, mul_one, abs_mul, abs_of_pos hd]
    exact mul_le_mul_of_nonneg_right hb hd.le
theorem translateFamily_mem_collinearQuadsR4 {d ϑ : ℝ} (h : IsScaleShape d ϑ)
    (hϑ : ϑ ≤ collinearThetaBound) {y e : Fin 4 → ℝ} {t : ℝ} (he : euclidNormVec e = 1)
    (ht : SpacingCondition t) :
    translateFamily (radialBump d) (equallySpacedPoints y e t d) ∈ collinearQuadsR4 d ϑ := by
  have hd := h.1
  refine ⟨⟨h, fun i => ⟨isLipschitzFor_translate_radialBump hd _, fun z => radialBump_nonneg _ _⟩,
    fun i j hij => ?_⟩, equallySpacedPoints y e t d,
    ⟨e, he, fun i j => ⟨_, equallySpacedPoints_sub y e t d i j⟩⟩,
    fun i => tsupport_translate_radialBump_subset hd _⟩
  refine ⟨equallySpacedPoints y e t d i, equallySpacedPoints y e t d j,
    isShapedBump_translate_radialBump hd h.2.1 hϑ _,
    isShapedBump_translate_radialBump hd h.2.1 hϑ _, ?_, ?_⟩
  · refine le_iInf₂ fun a ha => le_iInf₂ fun b hb => ENNReal.ofReal_le_ofReal ?_
    have ha' : euclidNormVec (a - equallySpacedPoints y e t d i) ≤ d / 16 :=
      tsupport_translate_radialBump_subset hd _ ha
    have hb' : euclidNormVec (b - equallySpacedPoints y e t d j) ≤ d / 16 :=
      tsupport_translate_radialBump_subset hd _ hb
    have h1 := abs_euclidNormVec_sub_le
      (equallySpacedPoints y e t d i - equallySpacedPoints y e t d j) (a - b)
    have h2 : (equallySpacedPoints y e t d i - equallySpacedPoints y e t d j) - (a - b) =
        (b - equallySpacedPoints y e t d j) - (a - equallySpacedPoints y e t d i) := by abel
    have h3 := euclidNormVec_sub_le (b - equallySpacedPoints y e t d j)
      (a - equallySpacedPoints y e t d i)
    rw [h2] at h1
    have h4 : 9 / 8 * d ≤
        euclidNormVec (equallySpacedPoints y e t d i - equallySpacedPoints y e t d j) := by
      rw [euclidNormVec_equallySpacedPoints_sub hd he ht]
      have h5 := one_le_abs_index_sub hij
      have h6 := ht.1
      have h7 : 9 / 8 ≤ |((i : ℕ) : ℝ) - ((j : ℕ) : ℝ)| * t := by nlinarith
      exact mul_le_mul_of_nonneg_right h7 hd.le
    have h5 := (abs_le.1 h1).2
    linarith
  · obtain ⟨u, hu, v, hv, huv⟩ := exists_close_points (y := y) hd he ht hij
    exact iInf₂_le_of_le u (closedBallR4_subset_tsupport hd _ hu)
      (iInf₂_le_of_le v (closedBallR4_subset_tsupport hd _ hv) (ENNReal.ofReal_le_ofReal huv))
theorem isPeriodizable_translateFamily {d ℓ : ℝ} (hd : 0 < d) (h40 : 40 * d ≤ ℓ)
    {y e : Fin 4 → ℝ} {t : ℝ} (he : euclidNormVec e = 1) (ht : SpacingCondition t) (i : Fin 4) :
    IsPeriodizable ℓ (closedBallR4 (equallySpacedPoints y e t d 0) (9 * d))
      (translateFamily (radialBump d) (equallySpacedPoints y e t d) i) := by
  refine ⟨fun x hx z hz => ?_, fun x hx => ?_⟩
  · have hx' : euclidNormVec (x - equallySpacedPoints y e t d 0) ≤ 9 * d := hx
    have hz' : euclidNormVec (z - equallySpacedPoints y e t d 0) ≤ 9 * d := hz
    have h1 := euclidNormVec_sub_le (x - equallySpacedPoints y e t d 0)
      (z - equallySpacedPoints y e t d 0)
    rw [sub_sub_sub_cancel_right] at h1
    linarith
  · have h1 : euclidNormVec (x - equallySpacedPoints y e t d i) ≤ d / 16 :=
      tsupport_translate_radialBump_subset hd _ (subset_tsupport _ hx)
    have h2 : euclidNormVec (equallySpacedPoints y e t d 0 - equallySpacedPoints y e t d i) ≤
        7 * d := by
      rw [euclidNormVec_equallySpacedPoints_sub hd he ht]
      have h3 := abs_index_sub_le_three 0 i
      have h4 := ht.2
      have h5 := ht.1
      have h6 : |(((0 : Fin 4) : ℕ) : ℝ) - ((i : ℕ) : ℝ)| * t ≤ 7 := by
        nlinarith [abs_nonneg ((((0 : Fin 4) : ℕ) : ℝ) - ((i : ℕ) : ℝ))]
      exact mul_le_mul_of_nonneg_right h6 hd.le
    have h3 := euclidNormVec_sub_le (x - equallySpacedPoints y e t d i)
      (equallySpacedPoints y e t d 0 - equallySpacedPoints y e t d i)
    rw [sub_sub_sub_cancel_right] at h3
    show euclidNormVec (x - equallySpacedPoints y e t d 0) ≤ 9 * d
    linarith
theorem collinearCentresStatement_of_collinear (hC : CollinearQuadruplesStatement) :
    CollinearCentresStatement := by
  obtain ⟨-, -, hAll⟩ := hC
  refine ⟨fun d ϑ h => ?_, collinearThetaBound_eq, collinearThetaBound_pos,
    collinearThetaBound_lt_zpow, fun d ϑ h hϑ y e t he ht => ?_⟩
  · obtain ⟨hS, hN, -, -, -, hT⟩ := hAll d ϑ h
    have hDir : ∀ g ∈ collinearQuadsR4 d ϑ, HasShapeAxisAlongCentres d g := by
      rintro g ⟨hg, c, ⟨e, he⟩, hc⟩
      exact ⟨e, c, he, hc, hS g e c hg he hc⟩
    refine ⟨hS, ⟨hN.1, hDir⟩, fun s h40 => ⟨(hT s h40).1.1, ?_⟩⟩
    rintro f ⟨-, g, hl, hg⟩
    exact ⟨g, hl, hg, hDir g hg⟩
  · have hd := h.1
    have hmem := translateFamily_mem_collinearQuadsR4 (y := y) h hϑ he ht
    obtain ⟨-, -, -, -, -, hT⟩ := hAll d ϑ h
    unfold BumpsInCollinearClassR4 PeriodizedBumpsInCollinearClassTorus
    rw [bumpsCentredAt_eq hd]
    refine ⟨⟨euclideanTSupport_rescaledBump hd, fun i => ?_, hmem⟩, fun s h40 =>
      ⟨fun i => isPeriodizable_translateFamily hd h40 he ht i, ?_⟩⟩
    · exact (contDiff_radialBump d).comp (contDiff_id.sub contDiff_const)
    · obtain ⟨-, -, -, -, hTA, -⟩ := hT s h40
      exact (hTA _ hmem.1).2.2.2 hmem
end QuadrupleClasses.CollinearCentres
end YangMills.Construction
