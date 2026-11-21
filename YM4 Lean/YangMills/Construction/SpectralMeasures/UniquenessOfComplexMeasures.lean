import YangMills.Construction.Continuum.CostOfTheModesOfASeparatedSystemProof
import YangMills.Construction.Matrices.CharactersOfGProof
import YangMills.Construction.SpectralMeasures.CalculusOfBorelFunctionsOnEuclideanSpaceProof
import YangMills.Construction.SpectralMeasures.DeterminingFamilies
import YangMills.Construction.SpectralMeasures.WeightedComplexMeasures
import Mathlib
set_option autoImplicit false
open MeasureTheory Filter Topology
noncomputable section
namespace YangMills.Construction.EuclideanBorel.MeasureUniqueness
variable {n : ℕ}
theorem integrable_exp_neg_mul_normSq (b : ℝ) (hb : 0 < b) :
    Integrable (fun v : Space n => Real.exp (-b * ‖v‖ ^ 2)) := by
  have hg := GaussianFourier.integrable_cexp_neg_mul_sq_norm_add (V := Space n) (b := (b : ℂ))
    (by simpa using hb) 0 0
  refine hg.re.congr (Eventually.of_forall fun v => ?_)
  have : Complex.exp (-(b : ℂ) * (‖v‖ : ℂ) ^ 2 + 0 * ((inner ℝ (0 : Space n) v : ℝ) : ℂ)) =
      ((Real.exp (-b * ‖v‖ ^ 2) : ℝ) : ℂ) := by
    push_cast
    simp
  simp only [RCLike.re_to_complex]
  rw [this, Complex.ofReal_re]
theorem integral_cexp_inner_mul_gaussian (b : ℝ) (hb : 0 < b) (w : Space n) :
    ∫ v : Space n, Complex.exp (Complex.I * ((inner ℝ w v : ℝ) : ℂ)) *
        ((Real.exp (-b * ‖v‖ ^ 2) : ℝ) : ℂ) =
      (((Real.pi / b) ^ ((n : ℝ) / 2) * Real.exp (-‖w‖ ^ 2 / (4 * b)) : ℝ) : ℂ) := by
  have hg := GaussianFourier.integral_cexp_neg_mul_sq_norm_add (V := Space n) (b := (b : ℂ))
    (by simpa using hb) Complex.I w
  have e1 : ∀ v : Space n, Complex.exp (Complex.I * ((inner ℝ w v : ℝ) : ℂ)) *
      ((Real.exp (-b * ‖v‖ ^ 2) : ℝ) : ℂ) =
      Complex.exp (-(b : ℂ) * (‖v‖ : ℂ) ^ 2 + Complex.I * ((inner ℝ w v : ℝ) : ℂ)) := by
    intro v
    rw [add_comm, Complex.exp_add]
    push_cast
    rfl
  simp_rw [e1]
  rw [hg]
  have hb' : (0 : ℝ) ≤ Real.pi / b := by positivity
  have e2 : ((Real.pi : ℂ) / (b : ℂ)) ^ ((Module.finrank ℝ (Space n) : ℂ) / 2) =
      (((Real.pi / b) ^ ((n : ℝ) / 2) : ℝ) : ℂ) := by
    rw [Complex.ofReal_cpow hb']
    simp
  have e3 : Complex.exp (Complex.I ^ 2 * (‖w‖ : ℂ) ^ 2 / (4 * (b : ℂ))) =
      ((Real.exp (-‖w‖ ^ 2 / (4 * b)) : ℝ) : ℂ) := by
    push_cast
    rw [Complex.I_sq]
    congr 1
    ring
  rw [e2, e3]
  push_cast
  rfl
theorem gaussianDecay_eq_exp (ε : ℝ) (v : Space n) :
    gaussianDecay ε v = Real.exp (-(ε / 2) * ‖v‖ ^ 2) := by
  unfold gaussianDecay
  congr 1
  ring
theorem heatKernel_eq_exp (ε : ℝ) (y : Space n) :
    heatKernel ε y =
      (2 * Real.pi * ε) ^ (-(n : ℝ) / 2) * Real.exp (-(1 / (2 * ε)) * ‖y‖ ^ 2) := by
  unfold heatKernel
  congr 2
  ring
theorem heatKernel_pos {ε : ℝ} (hε : 0 < ε) (y : Space n) : 0 < heatKernel ε y := by
  unfold heatKernel
  have : 0 < 2 * Real.pi * ε := by positivity
  positivity
theorem integrable_gaussianDecay {ε : ℝ} (hε : 0 < ε) :
    Integrable (gaussianDecay ε : Space n → ℝ) := by
  have hg := integrable_exp_neg_mul_normSq (n := n) (ε / 2) (by positivity)
  refine hg.congr (Eventually.of_forall fun v => ?_)
  exact (gaussianDecay_eq_exp ε v).symm
theorem integrable_heatKernel {ε : ℝ} (hε : 0 < ε) :
    Integrable (heatKernel ε : Space n → ℝ) := by
  have hg := (integrable_exp_neg_mul_normSq (n := n) (1 / (2 * ε)) (by positivity)).const_mul
    ((2 * Real.pi * ε) ^ (-(n : ℝ) / 2))
  refine hg.congr (Eventually.of_forall fun v => ?_)
  exact (heatKernel_eq_exp ε v).symm
theorem continuous_heatKernel (ε : ℝ) : Continuous (heatKernel ε : Space n → ℝ) := by
  unfold heatKernel
  fun_prop
theorem heatKernel_neg (ε : ℝ) (y : Space n) : heatKernel ε (-y) = heatKernel ε y := by
  unfold heatKernel
  rw [norm_neg]
theorem integral_heatKernel {ε : ℝ} (hε : 0 < ε) :
    ∫ y : Space n, heatKernel ε y = 1 := by
  simp_rw [heatKernel_eq_exp]
  rw [integral_const_mul, GaussianFourier.integral_rexp_neg_mul_sq_norm (by positivity)]
  have h1 : Real.pi / (1 / (2 * ε)) = 2 * Real.pi * ε := by
    field_simp
  have h2 : (0 : ℝ) < 2 * Real.pi * ε := by positivity
  rw [h1]
  simp only [finrank_euclideanSpace, Fintype.card_fin]
  rw [← Real.rpow_add h2]
  have : -(n : ℝ) / 2 + (n : ℝ) / 2 = 0 := by ring
  rw [this, Real.rpow_zero]
theorem gaussianFourierIdentities_holds {ε : ℝ} (hε : 0 < ε) : GaussianFourierIdentities n ε := by
  have h2 : (0 : ℝ) < 2 * Real.pi * ε := by positivity
  refine ⟨fun y => ?_, fun v => ?_, integral_heatKernel hε⟩
  · have hg := integral_cexp_inner_mul_gaussian (n := n) (ε / 2) (by positivity) y
    have e : ∀ v : Space n, Complex.exp (Complex.I * ((inner ℝ v y : ℝ) : ℂ)) *
        (gaussianDecay ε v : ℂ) = Complex.exp (Complex.I * ((inner ℝ y v : ℝ) : ℂ)) *
        ((Real.exp (-(ε / 2) * ‖v‖ ^ 2) : ℝ) : ℂ) := by
      intro v
      rw [gaussianDecay_eq_exp, real_inner_comm]
    simp_rw [e]
    rw [hg]
    congr 1
    unfold heatKernel
    have h3 : Real.pi / (ε / 2) = (2 * Real.pi) ^ 2 * (2 * Real.pi * ε)⁻¹ := by
      field_simp
    have h4 : -‖y‖ ^ 2 / (4 * (ε / 2)) = -(‖y‖ ^ 2) / (2 * ε) := by
      field_simp
      ring
    rw [h3, h4, ← mul_assoc]
    congr 1
    have hp : (0 : ℝ) ≤ (2 * Real.pi) ^ 2 := by positivity
    rw [Real.mul_rpow hp (by positivity), ← Real.rpow_natCast (2 * Real.pi) 2,
      ← Real.rpow_mul (by positivity), Real.inv_rpow h2.le, ← Real.rpow_neg h2.le]
    congr 1
    · rw [← Real.rpow_natCast]
      congr 1
      push_cast
      ring
    · congr 1
      ring
  · have hg := integral_cexp_inner_mul_gaussian (n := n) (1 / (2 * ε)) (by positivity) v
    have e : ∀ y : Space n, Complex.exp (Complex.I * ((inner ℝ v y : ℝ) : ℂ)) *
        (heatKernel ε y : ℂ) = (((2 * Real.pi * ε) ^ (-(n : ℝ) / 2) : ℝ) : ℂ) *
        (Complex.exp (Complex.I * ((inner ℝ v y : ℝ) : ℂ)) *
        ((Real.exp (-(1 / (2 * ε)) * ‖y‖ ^ 2) : ℝ) : ℂ)) := by
      intro y
      rw [heatKernel_eq_exp]
      push_cast
      ring
    simp_rw [e]
    rw [integral_const_mul, hg]
    have h3 : Real.pi / (1 / (2 * ε)) = 2 * Real.pi * ε := by
      field_simp
    have h4 : -‖v‖ ^ 2 / (4 * (1 / (2 * ε))) = -(ε * ‖v‖ ^ 2) / 2 := by
      field_simp
      ring
    rw [h3, h4, ← Complex.ofReal_mul, ← mul_assoc, ← Real.rpow_add h2]
    have : -(n : ℝ) / 2 + (n : ℝ) / 2 = 0 := by ring
    rw [this, Real.rpow_zero, one_mul]
    rfl
theorem norm_cexp_I_mul_ofReal (r : ℝ) : ‖Complex.exp (Complex.I * (r : ℂ))‖ = 1 := by apply _root_.YangMills.Construction.ConfigSpace.ModeCost.norm_exp_I_mul_ofReal <;> assumption
theorem norm_cexp_neg_I_mul_ofReal (r : ℝ) : ‖Complex.exp (-(Complex.I * (r : ℂ)))‖ = 1 := by apply _root_.YangMills.Construction.SpinHarmonics.SpinCharacters.norm_cexp_neg_I_mul <;> assumption
theorem heatKernel_le_peak {ε : ℝ} (hε : 0 < ε) (y : Space n) :
    heatKernel ε y ≤ (2 * Real.pi * ε) ^ (-(n : ℝ) / 2) := by
  unfold heatKernel
  have hle : Real.exp (-(‖y‖ ^ 2) / (2 * ε)) ≤ 1 := by
    rw [Real.exp_le_one_iff]
    have : 0 ≤ ‖y‖ ^ 2 / (2 * ε) := by positivity
    rw [neg_div]
    linarith
  have h2 : (0 : ℝ) < 2 * Real.pi * ε := by positivity
  exact mul_le_of_le_one_right (Real.rpow_nonneg h2.le _) hle
section Mollifier
variable {h : Space n → ℂ}
theorem hasCompactSupport_of_boundedlySupported (hh : h ∈ boundedlySupportedContinuous n) :
    HasCompactSupport h := by
  obtain ⟨_, B, hB, hz⟩ := hh
  refine HasCompactSupport.of_support_subset_isCompact hB.isCompact_closure ?_
  intro y hy
  exact subset_closure (by_contra fun hn => hy (hz y hn))
theorem boundedlySupported_of_hasCompactSupport (hc : Continuous h) (hs : HasCompactSupport h) :
    h ∈ boundedlySupportedContinuous n := by
  refine ⟨hc, tsupport h, hs.isCompact.isBounded, fun y hy => ?_⟩
  exact image_eq_zero_of_notMem_tsupport hy
theorem integrable_of_boundedlySupported (hh : h ∈ boundedlySupportedContinuous n) :
    Integrable h :=
  hh.1.integrable_of_hasCompactSupport (hasCompactSupport_of_boundedlySupported hh)
theorem exists_norm_bound_of_boundedlySupported (hh : h ∈ boundedlySupportedContinuous n) :
    ∃ S : ℝ, 0 ≤ S ∧ ∀ y, ‖h y‖ ≤ S := by
  obtain ⟨S, hS⟩ := (hasCompactSupport_of_boundedlySupported hh).exists_bound_of_continuous hh.1
  exact ⟨S, (norm_nonneg _).trans (hS 0), hS⟩
theorem bddAbove_range_norm_of_le {f : Space n → ℂ} {S : ℝ} (hS : ∀ y, ‖f y‖ ≤ S) :
    BddAbove (Set.range fun y => ‖f y‖) :=
  ⟨S, by rintro _ ⟨y, rfl⟩; exact hS y⟩
theorem integrable_heatKernelConv_integrand (hh : h ∈ boundedlySupportedContinuous n)
    {ε : ℝ} (hε : 0 < ε) (y : Space n) :
    Integrable fun y' => h y' * (heatKernel ε (y - y') : ℂ) := by
  refine (integrable_of_boundedlySupported hh).mul_bdd
    (c := (2 * Real.pi * ε) ^ (-(n : ℝ) / 2)) ?_ ?_
  · have := continuous_heatKernel (n := n) ε
    exact (by fun_prop : Continuous fun y' => (heatKernel ε (y - y') : ℂ)).aestronglyMeasurable
  · refine Eventually.of_forall fun y' => ?_
    rw [Complex.norm_real, Real.norm_of_nonneg (heatKernel_pos hε _).le]
    exact heatKernel_le_peak hε _
theorem continuous_heatKernelConv (hh : h ∈ boundedlySupportedContinuous n)
    {ε : ℝ} (hε : 0 < ε) : Continuous (heatKernelConv h ε) := by
  have hG := continuous_heatKernel (n := n) ε
  unfold heatKernelConv
  refine continuous_of_dominated
    (bound := fun y' => ‖h y'‖ * (2 * Real.pi * ε) ^ (-(n : ℝ) / 2)) (fun y => ?_) (fun y => ?_)
    ((integrable_of_boundedlySupported hh).norm.mul_const _) (Eventually.of_forall fun y' => ?_)
  · exact (integrable_heatKernelConv_integrand hh hε y).aestronglyMeasurable
  · refine Eventually.of_forall fun y' => ?_
    rw [norm_mul, Complex.norm_real, Real.norm_of_nonneg (heatKernel_pos hε _).le]
    exact mul_le_mul_of_nonneg_left (heatKernel_le_peak hε _) (norm_nonneg _)
  · fun_prop
theorem tendsto_heatKernel_sub_atInfty {ε : ℝ} (hε : 0 < ε) (y' : Space n) :
    Tendsto (fun y : Space n => heatKernel ε (y - y')) (comap (fun y => ‖y‖) atTop)
      (𝓝 0) := by
  have ht : Tendsto (fun y : Space n => ‖y - y'‖) (comap (fun y => ‖y‖) atTop) atTop := by
    refine tendsto_atTop_mono (f := fun y : Space n => ‖y‖ - ‖y'‖)
      (fun y => norm_sub_norm_le y y') ?_
    exact tendsto_atTop_add_const_right _ _ tendsto_comap
  have h1 : Tendsto (fun t : ℝ => -(t ^ 2 / (2 * ε))) atTop atBot :=
    tendsto_neg_atTop_atBot.comp
      ((tendsto_pow_atTop two_ne_zero).atTop_div_const (by positivity))
  have h2 : Tendsto (fun y : Space n => Real.exp (-(‖y - y'‖ ^ 2 / (2 * ε))))
      (comap (fun y => ‖y‖) atTop) (𝓝 0) :=
    Real.tendsto_exp_atBot.comp (h1.comp ht)
  have h3 := h2.const_mul ((2 * Real.pi * ε) ^ (-(n : ℝ) / 2))
  rw [mul_zero] at h3
  refine h3.congr fun y => ?_
  unfold heatKernel
  congr 2
  ring
theorem tendsto_heatKernelConv_atInfty (hh : h ∈ boundedlySupportedContinuous n)
    {ε : ℝ} (hε : 0 < ε) :
    Tendsto (heatKernelConv h ε) (comap (fun y => ‖y‖) atTop) (𝓝 0) := by
  have hlim : Tendsto (fun y : Space n => ∫ y', h y' * (heatKernel ε (y - y') : ℂ))
      (comap (fun y => ‖y‖) atTop) (𝓝 (∫ _ : Space n, (0 : ℂ))) := by
    refine tendsto_integral_filter_of_dominated_convergence
      (fun y' => ‖h y'‖ * (2 * Real.pi * ε) ^ (-(n : ℝ) / 2))
      (Eventually.of_forall fun y => (integrable_heatKernelConv_integrand hh hε y).aestronglyMeasurable)
      (Eventually.of_forall fun y => Eventually.of_forall fun y' => ?_)
      ((integrable_of_boundedlySupported hh).norm.mul_const _) (Eventually.of_forall fun y' => ?_)
    · rw [norm_mul, Complex.norm_real, Real.norm_of_nonneg (heatKernel_pos hε _).le]
      exact mul_le_mul_of_nonneg_left (heatKernel_le_peak hε _) (norm_nonneg _)
    · have h1 := (Complex.continuous_ofReal.tendsto 0).comp (tendsto_heatKernel_sub_atInfty hε y')
      have h2 := h1.const_mul (h y')
      simpa using h2
  rw [integral_zero] at hlim
  exact hlim
def normHeatKernelConv (h : Space n → ℂ) (ε : ℝ) : Space n → ℝ :=
  convolution (fun y => ‖h y‖) (heatKernel ε) (ContinuousLinearMap.mul ℝ ℝ) volume
theorem normHeatKernelConv_apply (h : Space n → ℂ) (ε : ℝ) (y : Space n) :
    normHeatKernelConv h ε y = ∫ y', ‖h y'‖ * heatKernel ε (y - y') := rfl
theorem norm_heatKernelConv_le {ε : ℝ} (hε : 0 < ε) (y : Space n) :
    ‖heatKernelConv h ε y‖ ≤ normHeatKernelConv h ε y := by
  rw [normHeatKernelConv_apply]
  refine (norm_integral_le_integral_norm _).trans (le_of_eq ?_)
  refine integral_congr_ae (Eventually.of_forall fun y' => ?_)
  simp only [norm_mul, Complex.norm_real, Real.norm_of_nonneg (heatKernel_pos hε _).le]
theorem integrable_normHeatKernelConv (hh : h ∈ boundedlySupportedContinuous n)
    {ε : ℝ} (hε : 0 < ε) : Integrable (normHeatKernelConv h ε) :=
  (integrable_of_boundedlySupported hh).norm.integrable_convolution _ (integrable_heatKernel hε)
theorem integral_normHeatKernelConv (hh : h ∈ boundedlySupportedContinuous n)
    {ε : ℝ} (hε : 0 < ε) : ∫ y, normHeatKernelConv h ε y = ∫ y, ‖h y‖ := by
  have := integral_convolution (μ := (volume : Measure (Space n))) (ν := volume)
    (ContinuousLinearMap.mul ℝ ℝ) (integrable_of_boundedlySupported hh).norm
    (integrable_heatKernel hε)
  rw [integral_heatKernel hε] at this
  simpa [normHeatKernelConv] using this
theorem integrable_heatKernelConv (hh : h ∈ boundedlySupportedContinuous n)
    {ε : ℝ} (hε : 0 < ε) : Integrable (heatKernelConv h ε) :=
  (integrable_normHeatKernelConv hh hε).mono' (continuous_heatKernelConv hh hε).aestronglyMeasurable
    (Eventually.of_forall fun y => norm_heatKernelConv_le hε y)
theorem integral_norm_heatKernelConv_le (hh : h ∈ boundedlySupportedContinuous n)
    {ε : ℝ} (hε : 0 < ε) :
    ∫ y, ‖heatKernelConv h ε y‖ ≤ ∫ y, ‖h y‖ := by
  rw [← integral_normHeatKernelConv hh hε]
  exact integral_mono (integrable_heatKernelConv hh hε).norm (integrable_normHeatKernelConv hh hε)
    fun y => norm_heatKernelConv_le hε y
theorem norm_heatKernelConv_le_of_bound (hh : h ∈ boundedlySupportedContinuous n)
    {ε : ℝ} (hε : 0 < ε) {S : ℝ} (hS : ∀ y, ‖h y‖ ≤ S) (y : Space n) :
    ‖heatKernelConv h ε y‖ ≤ S := by
  refine (norm_heatKernelConv_le hε y).trans ?_
  rw [normHeatKernelConv_apply]
  have hi : Integrable fun y' : Space n => heatKernel ε (y - y') :=
    (integrable_heatKernel hε).comp_sub_left y
  have h1 : ∫ y', ‖h y'‖ * heatKernel ε (y - y') ≤ ∫ y', S * heatKernel ε (y - y') := by
    refine integral_mono ?_ (hi.const_mul S) fun y' => ?_
    · exact (integrable_heatKernelConv_integrand hh hε y).norm.congr
        (Eventually.of_forall fun y' => by
          simp only [norm_mul, Complex.norm_real,
            Real.norm_of_nonneg (heatKernel_pos hε _).le])
    · exact mul_le_mul_of_nonneg_right (hS y') (heatKernel_pos hε _).le
  refine h1.trans (le_of_eq ?_)
  rw [integral_const_mul, integral_sub_left_eq_self (heatKernel ε : Space n → ℝ) volume y,
    integral_heatKernel hε, mul_one]
theorem heatKernelConv_real_nonneg {ε : ℝ} (hε : 0 < ε)
    (hpos : ∀ y, (h y).im = 0 ∧ 0 ≤ (h y).re) (y : Space n) :
    (heatKernelConv h ε y).im = 0 ∧
      0 ≤ (heatKernelConv h ε y).re := by
  have e : heatKernelConv h ε y =
      ((∫ y', (h y').re * heatKernel ε (y - y') : ℝ) : ℂ) := by
    rw [← integral_complex_ofReal]
    refine integral_congr_ae (Eventually.of_forall fun y' => ?_)
    have : h y' = ((h y').re : ℂ) := by
      apply Complex.ext <;> simp [(hpos y').1]
    simp only []
    push_cast
    rw [← this]
  rw [e, Complex.ofReal_im, Complex.ofReal_re]
  exact ⟨rfl, integral_nonneg fun y' => mul_nonneg (hpos y').2 (heatKernel_pos hε _).le⟩
end Mollifier
section Approximation
variable {h : Space n → ℂ}
theorem heatKernel_le_mul_heatKernel_two_mul {ε δ : ℝ} (hε : 0 < ε) (hδ : 0 ≤ δ) {w : Space n}
    (hw : δ ≤ ‖w‖) :
    heatKernel ε w ≤
      (2 : ℝ) ^ ((n : ℝ) / 2) * Real.exp (-(δ ^ 2) / (4 * ε)) * heatKernel (2 * ε) w := by
  unfold heatKernel
  have hx : (0 : ℝ) < 2 * Real.pi * ε := by positivity
  have e1 : 2 * Real.pi * (2 * ε) = 2 * (2 * Real.pi * ε) := by ring
  rw [e1, Real.mul_rpow (by norm_num) hx.le]
  have e2 : (2 : ℝ) ^ ((n : ℝ) / 2) * (2 : ℝ) ^ (-(n : ℝ) / 2) = 1 := by
    rw [← Real.rpow_add (by norm_num)]
    have : (n : ℝ) / 2 + -(n : ℝ) / 2 = 0 := by ring
    rw [this, Real.rpow_zero]
  have hexp : Real.exp (-(‖w‖ ^ 2) / (2 * ε)) ≤
      Real.exp (-(δ ^ 2) / (4 * ε)) * Real.exp (-(‖w‖ ^ 2) / (2 * (2 * ε))) := by
    rw [← Real.exp_add]
    apply Real.exp_le_exp.2
    have hsq : δ ^ 2 ≤ ‖w‖ ^ 2 := pow_le_pow_left₀ hδ hw 2
    have h4 : 0 < 4 * ε := by positivity
    have a1 : -(‖w‖ ^ 2) / (2 * ε) = (-2 * ‖w‖ ^ 2) / (4 * ε) := by
      field_simp
      ring
    have a2 : -(‖w‖ ^ 2) / (2 * (2 * ε)) = (-(‖w‖ ^ 2)) / (4 * ε) := by
      congr 1
      ring
    rw [a1, a2, ← add_div]
    exact div_le_div_of_nonneg_right (by linarith) h4.le
  calc (2 * Real.pi * ε) ^ (-(n : ℝ) / 2) * Real.exp (-(‖w‖ ^ 2) / (2 * ε))
      ≤ (2 * Real.pi * ε) ^ (-(n : ℝ) / 2) * (Real.exp (-(δ ^ 2) / (4 * ε)) *
          Real.exp (-(‖w‖ ^ 2) / (2 * (2 * ε)))) :=
        mul_le_mul_of_nonneg_left hexp (Real.rpow_nonneg hx.le _)
    _ = _ := by
        linear_combination (-((2 * Real.pi * ε) ^ (-(n : ℝ) / 2) *
          (Real.exp (-(δ ^ 2) / (4 * ε)) * Real.exp (-(‖w‖ ^ 2) / (2 * (2 * ε)))))) * e2
theorem norm_heatKernelConv_sub_le (hh : h ∈ boundedlySupportedContinuous n)
    {ε : ℝ} (hε : 0 < ε) {S δ η : ℝ} (hS0 : 0 ≤ S) (hS : ∀ y, ‖h y‖ ≤ S) (hδ : 0 ≤ δ) (hη : 0 ≤ η)
    (huc : ∀ y w : Space n, ‖w‖ ≤ δ → ‖h (y - w) - h y‖ ≤ η) (y : Space n) :
    ‖heatKernelConv h ε y - h y‖ ≤
      η + 2 * S * ((2 : ℝ) ^ ((n : ℝ) / 2) * Real.exp (-(δ ^ 2) / (4 * ε))) := by
  have hε2 : 0 < 2 * ε := by positivity
  have hsub : heatKernelConv h ε y =
      ∫ w, h (y - w) * (heatKernel ε w : ℂ) := by
    have := integral_sub_left_eq_self (fun w => h (y - w) * (heatKernel ε w : ℂ)) volume y
    simpa [heatKernelConv] using this
  have hi1 : Integrable fun w => h (y - w) * (heatKernel ε w : ℂ) := by
    have := (integrable_heatKernelConv_integrand hh hε y).comp_sub_left y
    simpa using this
  have hGc : Integrable fun w : Space n => (heatKernel ε w : ℂ) :=
    (integrable_heatKernel hε).ofReal
  have hy : ∫ w : Space n, h y * (heatKernel ε w : ℂ) = h y := by
    rw [integral_const_mul, integral_complex_ofReal, integral_heatKernel hε]
    simp
  have hd : heatKernelConv h ε y - h y =
      ∫ w, (h (y - w) - h y) * (heatKernel ε w : ℂ) := by
    have h1 := integral_sub hi1 (hGc.const_mul (h y))
    rw [hy] at h1
    rw [hsub, ← h1]
    refine integral_congr_ae (Eventually.of_forall fun w => ?_)
    simp only []
    ring
  rw [hd]
  set c : ℝ := (2 : ℝ) ^ ((n : ℝ) / 2) * Real.exp (-(δ ^ 2) / (4 * ε)) with hc
  have hb : ∀ w : Space n, ‖(h (y - w) - h y) * (heatKernel ε w : ℂ)‖ ≤
      η * heatKernel ε w + 2 * S * c * heatKernel (2 * ε) w := by
    intro w
    have hG := (heatKernel_pos hε w).le
    have hG2 := (heatKernel_pos hε2 w).le
    rw [norm_mul, Complex.norm_real, Real.norm_of_nonneg hG]
    rcases le_total ‖w‖ δ with hw | hw
    · have := mul_le_mul_of_nonneg_right (huc y w hw) hG
      have h2 : 0 ≤ 2 * S * c * heatKernel (2 * ε) w := by positivity
      linarith
    · have h1 : ‖h (y - w) - h y‖ ≤ 2 * S := by
        refine (norm_sub_le _ _).trans ?_
        linarith [hS (y - w), hS y]
      have h2 := heatKernel_le_mul_heatKernel_two_mul hε hδ hw
      have h3 : ‖h (y - w) - h y‖ * heatKernel ε w ≤ 2 * S * (c * heatKernel (2 * ε) w) :=
        mul_le_mul h1 h2 hG (by positivity)
      have h4 : 0 ≤ η * heatKernel ε w := by positivity
      linarith
  have hi2 : Integrable fun w : Space n =>
      η * heatKernel ε w + 2 * S * c * heatKernel (2 * ε) w :=
    ((integrable_heatKernel hε).const_mul _).add ((integrable_heatKernel hε2).const_mul _)
  refine (norm_integral_le_of_norm_le hi2 (Eventually.of_forall hb)).trans (le_of_eq ?_)
  rw [integral_add ((integrable_heatKernel hε).const_mul _)
    ((integrable_heatKernel hε2).const_mul _), integral_const_mul, integral_const_mul,
    integral_heatKernel hε, integral_heatKernel hε2]
  ring
theorem tendsto_iSup_norm_heatKernelConv_sub (hh : h ∈ boundedlySupportedContinuous n) :
    Tendsto (fun ε : ℝ => ⨆ y, ‖heatKernelConv h ε y - h y‖) (𝓝[>] 0) (𝓝 0) := by
  obtain ⟨S, hS0, hS⟩ := exists_norm_bound_of_boundedlySupported hh
  have huc := (hasCompactSupport_of_boundedlySupported hh).uniformContinuous_of_continuous hh.1
  rw [Metric.tendsto_nhds]
  intro e he
  obtain ⟨δ, hδ, hd⟩ := Metric.uniformContinuous_iff.1 huc (e / 4) (by positivity)
  have hδ2 : 0 < δ / 2 := by positivity
  have hc : Tendsto (fun ε : ℝ => 2 * S * ((2 : ℝ) ^ ((n : ℝ) / 2) *
      Real.exp (-((δ / 2) ^ 2) / (4 * ε)))) (𝓝[>] 0) (𝓝 0) := by
    have h1 : Tendsto (fun ε : ℝ => -((δ / 2) ^ 2) / (4 * ε)) (𝓝[>] 0) atBot := by
      have h0 : -((δ / 2) ^ 2) / 4 < 0 := by
        have : 0 < (δ / 2) ^ 2 := by positivity
        linarith
      refine (tendsto_inv_nhdsGT_zero.const_mul_atTop_of_neg h0).congr fun ε => ?_
      rw [div_mul_eq_div_div, div_eq_mul_inv _ ε]
    have h2 := Real.tendsto_exp_atBot.comp h1
    have h3 := (h2.const_mul ((2 : ℝ) ^ ((n : ℝ) / 2))).const_mul (2 * S)
    simpa using h3
  have hpos : (0 : ℝ) < e / 4 := by positivity
  filter_upwards [self_mem_nhdsWithin, hc.eventually (Iio_mem_nhds hpos)] with ε hε hcε
  have hε' : (0 : ℝ) < ε := hε
  have hle : ⨆ y, ‖heatKernelConv h ε y - h y‖ ≤
      e / 4 + 2 * S * ((2 : ℝ) ^ ((n : ℝ) / 2) * Real.exp (-((δ / 2) ^ 2) / (4 * ε))) := by
    refine ciSup_le fun y => norm_heatKernelConv_sub_le hh hε' hS0 hS hδ2.le hpos.le ?_ y
    intro y w hw
    have : dist (y - w) y < δ := by
      rw [dist_eq_norm]
      simp only [sub_sub_cancel_left, norm_neg]
      linarith
    have := hd this
    rw [dist_eq_norm] at this
    exact this.le
  have h0 : 0 ≤ ⨆ y, ‖heatKernelConv h ε y - h y‖ :=
    Real.iSup_nonneg fun _ => norm_nonneg _
  rw [Real.dist_eq, sub_zero, abs_of_nonneg h0]
  have : 2 * S * ((2 : ℝ) ^ ((n : ℝ) / 2) * Real.exp (-((δ / 2) ^ 2) / (4 * ε))) < e / 4 := hcε
  linarith
theorem continuous_cexp_neg_inner_left (y' : Space n) : Continuous fun v : Space n =>
    Complex.exp (-(Complex.I * ((inner ℝ v y' : ℝ) : ℂ))) := by
  fun_prop
theorem continuous_cexp_neg_inner_right (v : Space n) : Continuous fun y' : Space n =>
    Complex.exp (-(Complex.I * ((inner ℝ v y' : ℝ) : ℂ))) := by
  fun_prop
theorem integrable_mul_cexp_neg_inner (hh : h ∈ boundedlySupportedContinuous n)
    (v : Space n) :
    Integrable fun y' => h y' * Complex.exp (-(Complex.I * ((inner ℝ v y' : ℝ) : ℂ))) :=
  (integrable_of_boundedlySupported hh).mul_bdd (c := 1)
    (continuous_cexp_neg_inner_right v).aestronglyMeasurable
    (Eventually.of_forall fun _ => (norm_cexp_neg_I_mul_ofReal _).le)
theorem fourierOfFnProperties_holds (hh : h ∈ boundedlySupportedContinuous n) :
    FourierOfFnProperties h := by
  refine ⟨?_, fun v => ?_⟩
  · unfold fourierOfFn
    refine continuous_of_dominated (bound := fun y' => ‖h y'‖)
      (fun v => (integrable_mul_cexp_neg_inner hh v).aestronglyMeasurable)
      (fun v => Eventually.of_forall fun y' => ?_) (integrable_of_boundedlySupported hh).norm
      (Eventually.of_forall fun y' => ?_)
    · rw [norm_mul, norm_cexp_neg_I_mul_ofReal, mul_one]
    · exact continuous_const.mul (continuous_cexp_neg_inner_left y')
  · refine (norm_integral_le_integral_norm _).trans (le_of_eq ?_)
    refine integral_congr_ae (Eventually.of_forall fun y' => ?_)
    simp only [norm_mul, norm_cexp_neg_I_mul_ofReal, mul_one]
theorem cexp_I_inner_sub (v y y' : Space n) :
    Complex.exp (Complex.I * ((inner ℝ v (y - y') : ℝ) : ℂ)) =
      Complex.exp (Complex.I * ((inner ℝ v y : ℝ) : ℂ)) *
        Complex.exp (-(Complex.I * ((inner ℝ v y' : ℝ) : ℂ))) := by
  rw [inner_sub_right, ← Complex.exp_add]
  congr 1
  push_cast
  ring
theorem heatKernel_eq_fourier_integral {ε : ℝ} (hε : 0 < ε) (y : Space n) :
    (heatKernel ε y : ℂ) = (((2 * Real.pi) ^ (-(n : ℤ)) : ℝ) : ℂ) *
      ∫ v : Space n, Complex.exp (Complex.I * ((inner ℝ v y : ℝ) : ℂ)) *
        (gaussianDecay ε v : ℂ) := by
  rw [(gaussianFourierIdentities_holds hε).1 y, ← Complex.ofReal_mul]
  congr 1
  have h2 : (2 * Real.pi) ≠ 0 := by positivity
  rw [← mul_assoc, zpow_neg, zpow_natCast, inv_mul_cancel₀ (pow_ne_zero n h2), one_mul]
theorem integral_heatKernel_mul_cexp_neg_inner {ε : ℝ} (hε : 0 < ε) (v : Space n) :
    ∫ w : Space n, (heatKernel ε w : ℂ) *
        Complex.exp (-(Complex.I * ((inner ℝ v w : ℝ) : ℂ))) = (gaussianDecay ε v : ℂ) := by
  rw [← (gaussianFourierIdentities_holds hε).2.1 v,
    ← integral_neg_eq_self (fun w : Space n => Complex.exp (Complex.I * ((inner ℝ v w : ℝ) : ℂ)) *
      (heatKernel ε w : ℂ)) volume]
  refine integral_congr_ae (Eventually.of_forall fun w => ?_)
  simp only [heatKernel_neg, inner_neg_right]
  push_cast
  rw [mul_neg, mul_comm]
theorem mollifiedFourierIdentities_holds (hh : h ∈ boundedlySupportedContinuous n)
    {ε : ℝ} (hε : 0 < ε) : MollifiedFourierIdentities h ε := by
  have hg := (integrable_gaussianDecay (n := n) hε).ofReal (𝕜 := ℂ)
  have hG := (integrable_heatKernel (n := n) hε).ofReal (𝕜 := ℂ)
  have hC := integrable_of_boundedlySupported hh
  refine ⟨fun y => ?_, fun v => ?_⟩
  · have hF : Integrable (Function.uncurry fun (y' v : Space n) =>
        h y' * (gaussianDecay ε v : ℂ) *
          Complex.exp (Complex.I * ((inner ℝ v (y - y') : ℝ) : ℂ)))
        ((volume : Measure (Space n)).prod volume) := by
      refine (hC.mul_prod hg).mul_bdd (c := 1) ?_ (Eventually.of_forall fun z => ?_)
      · exact (by fun_prop : Continuous fun z : Space n × Space n =>
          Complex.exp (Complex.I * ((inner ℝ z.2 (y - z.1) : ℝ) : ℂ))).aestronglyMeasurable
      · exact (norm_cexp_I_mul_ofReal _).le
    have hswap := integral_integral_swap hF
    have hl : heatKernelConv h ε y =
        (((2 * Real.pi) ^ (-(n : ℤ)) : ℝ) : ℂ) * ∫ y', ∫ v,
          h y' * (gaussianDecay ε v : ℂ) *
            Complex.exp (Complex.I * ((inner ℝ v (y - y') : ℝ) : ℂ)) := by
      unfold heatKernelConv
      rw [← integral_const_mul]
      refine integral_congr_ae (Eventually.of_forall fun y' => ?_)
      simp only []
      rw [heatKernel_eq_fourier_integral hε (y - y'), mul_left_comm, ← integral_const_mul (h y')]
      congr 1
      refine integral_congr_ae (Eventually.of_forall fun v => ?_)
      simp only []
      ring
    rw [hl, hswap]
    congr 1
    refine integral_congr_ae (Eventually.of_forall fun v => ?_)
    simp only [fourierOfFn]
    rw [← integral_const_mul]
    refine integral_congr_ae (Eventually.of_forall fun y' => ?_)
    simp only []
    rw [cexp_I_inner_sub]
    ring
  · have hF : Integrable (Function.uncurry fun (y y' : Space n) =>
        h y' * (heatKernel ε (y - y') : ℂ) *
          Complex.exp (-(Complex.I * ((inner ℝ v y : ℝ) : ℂ))))
        ((volume : Measure (Space n)).prod volume) := by
      have h0 := hC.convolution_integrand (μ := (volume : Measure (Space n)))
        (ContinuousLinearMap.mul ℂ ℂ) hG
      refine h0.mul_bdd (c := 1) ?_ (Eventually.of_forall fun z => ?_)
      · exact ((continuous_cexp_neg_inner_right v).comp continuous_fst).aestronglyMeasurable
      · exact (norm_cexp_neg_I_mul_ofReal _).le
    have hswap := integral_integral_swap hF
    have hl : ∫ y, heatKernelConv h ε y *
        Complex.exp (-(Complex.I * ((inner ℝ v y : ℝ) : ℂ))) =
        ∫ y, ∫ y', h y' * (heatKernel ε (y - y') : ℂ) *
          Complex.exp (-(Complex.I * ((inner ℝ v y : ℝ) : ℂ))) := by
      refine integral_congr_ae (Eventually.of_forall fun y => ?_)
      simp only [heatKernelConv]
      rw [integral_mul_const]
    rw [hl, hswap]
    have hin : ∀ y' : Space n, ∫ y, h y' * (heatKernel ε (y - y') : ℂ) *
        Complex.exp (-(Complex.I * ((inner ℝ v y : ℝ) : ℂ))) =
        (gaussianDecay ε v : ℂ) *
          (h y' * Complex.exp (-(Complex.I * ((inner ℝ v y' : ℝ) : ℂ)))) := by
      intro y'
      set F : Space n → ℂ := fun w =>
        (h y' * Complex.exp (-(Complex.I * ((inner ℝ v y' : ℝ) : ℂ)))) *
          ((heatKernel ε w : ℂ) * Complex.exp (-(Complex.I * ((inner ℝ v w : ℝ) : ℂ))))
        with hFdef
      have h1 := integral_sub_right_eq_self (μ := (volume : Measure (Space n))) F y'
      have h2 : ∫ w, F w = (h y' * Complex.exp (-(Complex.I * ((inner ℝ v y' : ℝ) : ℂ)))) *
          (gaussianDecay ε v : ℂ) := by
        simp only [hFdef]
        rw [integral_const_mul, integral_heatKernel_mul_cexp_neg_inner hε]
      rw [mul_comm (gaussianDecay ε v : ℂ), ← h2, ← h1]
      refine integral_congr_ae (Eventually.of_forall fun y => ?_)
      simp only [hFdef, inner_sub_right]
      have e : Complex.exp (-(Complex.I * ((inner ℝ v y : ℝ) : ℂ))) =
          Complex.exp (-(Complex.I * ((inner ℝ v y' : ℝ) : ℂ))) *
            Complex.exp (-(Complex.I * (((inner ℝ v y - inner ℝ v y' : ℝ)) : ℂ))) := by
        rw [← Complex.exp_add]
        congr 1
        push_cast
        ring
      rw [e]
      ring
    simp_rw [hin]
    rw [integral_const_mul]
    rfl
end Approximation
theorem exists_measureCombination {ν : BorelSubset n → ℂ} (hν : IsFiniteCombinationMeasure ν) :
    ∃ p : MeasureCombination n, p.toSetFunction = ν ∧ ∀ f, complexIntegral ν f = p.integral f := by
  refine ⟨Classical.choose hν, Classical.choose_spec hν, fun f => ?_⟩
  rw [complexIntegral, dif_pos hν]
def totalMass (p : MeasureCombination n) : ℝ :=
  ∑ j, ‖p.coeff j‖ * (p.component j).real Set.univ
theorem totalMass_nonneg (p : MeasureCombination n) : 0 ≤ totalMass p :=
  Finset.sum_nonneg fun _ _ => mul_nonneg (norm_nonneg _) measureReal_nonneg
theorem norm_combination_integral_le (p : MeasureCombination n) {f : Space n → ℂ} {M : ℝ}
    (hM : ∀ y, ‖f y‖ ≤ M) : ‖p.integral f‖ ≤ totalMass p * M := by
  unfold MeasureCombination.integral totalMass
  rw [Finset.sum_mul]
  refine (norm_sum_le _ _).trans (Finset.sum_le_sum fun j _ => ?_)
  have := p.isFinite j
  rw [norm_mul, mul_assoc]
  refine mul_le_mul_of_nonneg_left ?_ (norm_nonneg _)
  rw [mul_comm]
  exact norm_integral_le_of_norm_le_const (Eventually.of_forall hM)
theorem integrable_of_isBoundedMeasurableFn (μ : Measure (Space n)) [IsFiniteMeasure μ]
    {f : Space n → ℂ} (hf : IsBoundedMeasurableFn f) : Integrable f μ := by
  obtain ⟨hm, C, hC⟩ := hf
  exact Integrable.of_bound hm.aestronglyMeasurable C (Eventually.of_forall hC)
theorem combination_integral_sub (p : MeasureCombination n) {f g : Space n → ℂ}
    (hf : IsBoundedMeasurableFn f) (hg : IsBoundedMeasurableFn g) :
    p.integral (fun y => f y - g y) = p.integral f - p.integral g := by
  unfold MeasureCombination.integral
  rw [← Finset.sum_sub_distrib]
  refine Finset.sum_congr rfl fun j _ => ?_
  have := p.isFinite j
  rw [integral_sub (integrable_of_isBoundedMeasurableFn _ hf)
    (integrable_of_isBoundedMeasurableFn _ hg), mul_sub]
theorem combination_integral_add (p : MeasureCombination n) {f g : Space n → ℂ}
    (hf : IsBoundedMeasurableFn f) (hg : IsBoundedMeasurableFn g) :
    p.integral (fun y => f y + g y) = p.integral f + p.integral g := by
  unfold MeasureCombination.integral
  rw [← Finset.sum_add_distrib]
  refine Finset.sum_congr rfl fun j _ => ?_
  have := p.isFinite j
  rw [integral_add (integrable_of_isBoundedMeasurableFn _ hf)
    (integrable_of_isBoundedMeasurableFn _ hg), mul_add]
theorem combination_integral_const_mul (p : MeasureCombination n) (a : ℂ) (f : Space n → ℂ) :
    p.integral (fun y => a * f y) = a * p.integral f := by
  unfold MeasureCombination.integral
  rw [Finset.mul_sum]
  refine Finset.sum_congr rfl fun j _ => ?_
  rw [integral_const_mul, mul_left_comm]
theorem isBoundedMeasurableFn_of_continuous {f : Space n → ℂ} (hc : Continuous f) {S : ℝ}
    (hS : ∀ y, ‖f y‖ ≤ S) : IsBoundedMeasurableFn f :=
  ⟨hc.measurable, S, hS⟩
theorem eq_zero_of_norm_le_mul_forall_pos {a : ℂ} {M : ℝ} (hM : 0 ≤ M)
    (h : ∀ e : ℝ, 0 < e → ‖a‖ ≤ M * e) : a = 0 := by
  by_contra ha
  have hp : 0 < ‖a‖ := norm_pos_iff.2 ha
  have h2 := h (‖a‖ / (2 * (M + 1))) (by positivity)
  have h3 : M * (‖a‖ / (2 * (M + 1))) ≤ ‖a‖ / 2 := by
    rw [← mul_div_assoc, div_le_div_iff₀ (by positivity) (by norm_num)]
    nlinarith
  linarith
theorem continuous_fourier_finiteMeasure (μ : Measure (Space n)) [IsFiniteMeasure μ] :
    Continuous fun v : Space n =>
      ∫ y, Complex.exp (Complex.I * ((inner ℝ v y : ℝ) : ℂ)) ∂μ := by
  refine continuous_of_dominated (bound := fun _ => (1 : ℝ)) (fun v => ?_)
    (fun v => Eventually.of_forall fun y => (norm_cexp_I_mul_ofReal _).le) (integrable_const _)
    (Eventually.of_forall fun y => ?_)
  · exact (by fun_prop : Continuous fun y : Space n =>
      Complex.exp (Complex.I * ((inner ℝ v y : ℝ) : ℂ))).aestronglyMeasurable
  · fun_prop
theorem fourierOfMeasureProperties_holds {ν : BorelSubset n → ℂ}
    (hν : IsFiniteCombinationMeasure ν) : FourierOfMeasureProperties ν := by
  obtain ⟨p, _, hi⟩ := exists_measureCombination hν
  refine ⟨?_, totalMass p * 1, fun v => ?_⟩
  · have : fourierOfMeasure ν = fun v => ∑ j, p.coeff j *
        ∫ y, Complex.exp (Complex.I * ((inner ℝ v y : ℝ) : ℂ)) ∂(p.component j) := by
      funext v
      rw [fourierOfMeasure, hi]
      rfl
    rw [this]
    refine continuous_finsetSum _ fun j _ => continuous_const.mul ?_
    have := p.isFinite j
    exact continuous_fourier_finiteMeasure _
  · rw [fourierOfMeasure, hi]
    exact norm_combination_integral_le p fun y => (norm_cexp_I_mul_ofReal _).le
theorem integrable_gaussianDecay_mul_fourierOfFn {h : Space n → ℂ}
    (hh : h ∈ boundedlySupportedContinuous n) {ε : ℝ} (hε : 0 < ε) :
    Integrable fun v : Space n => (gaussianDecay ε v : ℂ) * fourierOfFn h v := by
  obtain ⟨hc, hb⟩ := fourierOfFnProperties_holds hh
  exact ((integrable_gaussianDecay (n := n) hε).ofReal (𝕜 := ℂ)).mul_bdd hc.aestronglyMeasurable
    (Eventually.of_forall hb)
theorem integral_heatKernelConv_finiteMeasure {h : Space n → ℂ}
    (hh : h ∈ boundedlySupportedContinuous n) {ε : ℝ} (hε : 0 < ε)
    (μ : Measure (Space n)) [IsFiniteMeasure μ] :
    ∫ y, heatKernelConv h ε y ∂μ =
      (((2 * Real.pi) ^ (-(n : ℤ)) : ℝ) : ℂ) *
        ∫ v : Space n, (gaussianDecay ε v : ℂ) * fourierOfFn h v *
          ∫ y, Complex.exp (Complex.I * ((inner ℝ v y : ℝ) : ℂ)) ∂μ := by
  have hA := integrable_gaussianDecay_mul_fourierOfFn hh hε
  have hF : Integrable (Function.uncurry fun (y v : Space n) =>
      Complex.exp (Complex.I * ((inner ℝ v y : ℝ) : ℂ)) *
        ((gaussianDecay ε v : ℂ) * fourierOfFn h v))
      (μ.prod (volume : Measure (Space n))) := by
    have h0 : Integrable (fun z : Space n × Space n =>
        (1 : ℂ) * ((gaussianDecay ε z.2 : ℂ) * fourierOfFn h z.2))
        (μ.prod (volume : Measure (Space n))) :=
      (integrable_const (1 : ℂ)).mul_prod hA
    have h1 := h0.bdd_mul (c := 1) (f := fun z : Space n × Space n =>
      Complex.exp (Complex.I * ((inner ℝ z.2 z.1 : ℝ) : ℂ)))
      (by fun_prop : Continuous fun z : Space n × Space n =>
        Complex.exp (Complex.I * ((inner ℝ z.2 z.1 : ℝ) : ℂ))).aestronglyMeasurable
      (Eventually.of_forall fun z => (norm_cexp_I_mul_ofReal _).le)
    refine h1.congr (Eventually.of_forall fun z => ?_)
    simp [Function.uncurry]
  have hswap := integral_integral_swap hF
  have hl : ∫ y, heatKernelConv h ε y ∂μ =
      (((2 * Real.pi) ^ (-(n : ℤ)) : ℝ) : ℂ) * ∫ y, (∫ v : Space n,
        Complex.exp (Complex.I * ((inner ℝ v y : ℝ) : ℂ)) *
          ((gaussianDecay ε v : ℂ) * fourierOfFn h v)) ∂μ := by
    rw [← integral_const_mul (((2 * Real.pi) ^ (-(n : ℤ)) : ℝ) : ℂ)]
    refine integral_congr_ae (Eventually.of_forall fun y => ?_)
    simp only []
    rw [(mollifiedFourierIdentities_holds hh hε).1 y]
    congr 2
    funext v
    ring
  rw [hl, hswap]
  congr 1
  refine integral_congr_ae (Eventually.of_forall fun v => ?_)
  simp only []
  rw [integral_mul_const, mul_comm]
theorem integralOfMollified_holds {ν : BorelSubset n → ℂ} (hν : IsFiniteCombinationMeasure ν)
    {h : Space n → ℂ} (hh : h ∈ boundedlySupportedContinuous n) {ε : ℝ} (hε : 0 < ε) :
    IntegralOfMollified ν h ε := by
  obtain ⟨p, _, hi⟩ := exists_measureCombination hν
  unfold IntegralOfMollified
  have hA := integrable_gaussianDecay_mul_fourierOfFn hh hε
  have hT : ∀ v, fourierOfMeasure ν v = ∑ j, p.coeff j *
      ∫ y, Complex.exp (Complex.I * ((inner ℝ v y : ℝ) : ℂ)) ∂(p.component j) := by
    intro v
    rw [fourierOfMeasure, hi]
    rfl
  have hint : ∀ j, Integrable fun v : Space n =>
      (gaussianDecay ε v : ℂ) * fourierOfFn h v * (p.coeff j *
        ∫ y, Complex.exp (Complex.I * ((inner ℝ v y : ℝ) : ℂ)) ∂(p.component j)) := by
    intro j
    have := p.isFinite j
    refine hA.mul_bdd (c := ‖p.coeff j‖ * ((1 : ℝ) * (p.component j).real Set.univ)) ?_
      (Eventually.of_forall fun v => ?_)
    · exact (continuous_const.mul
        (continuous_fourier_finiteMeasure (p.component j))).aestronglyMeasurable
    · rw [norm_mul]
      refine mul_le_mul_of_nonneg_left ?_ (norm_nonneg _)
      exact norm_integral_le_of_norm_le_const
        (Eventually.of_forall fun y => (norm_cexp_I_mul_ofReal _).le)
  simp_rw [hT, Finset.mul_sum]
  rw [integral_finsetSum _ fun j _ => hint j, hi, Finset.mul_sum]
  refine Finset.sum_congr rfl fun j _ => ?_
  have := p.isFinite j
  rw [integral_heatKernelConv_finiteMeasure hh hε]
  rw [mul_left_comm, ← integral_const_mul (p.coeff j)]
  congr 2
  funext v
  ring
theorem isZeroMeasure_of_integral_boundedlySupported {ν : BorelSubset n → ℂ}
    (hν : IsFiniteCombinationMeasure ν)
    (h0 : ∀ h' ∈ boundedlySupportedContinuous n, complexIntegral ν h' = 0) : IsZeroMeasure ν := by
  obtain ⟨p, hp, hi⟩ := exists_measureCombination hν
  intro Δ
  rw [← hp]
  have hfin := p.isFinite
  have hμ : IsFiniteMeasure (Measure.sum p.component) := by
    constructor
    rw [Measure.sum_apply _ MeasurableSet.univ, tsum_fintype]
    exact ENNReal.sum_lt_top.2 fun j _ => measure_lt_top _ _
  have hf : Integrable (Δ.1.indicator (1 : Space n → ℂ)) (Measure.sum p.component) :=
    (integrable_const (1 : ℂ)).indicator Δ.2
  have hval : p.toSetFunction Δ = p.integral (Δ.1.indicator 1) := by
    refine Finset.sum_congr rfl fun j _ => ?_
    have h1 : Δ.1.indicator (1 : Space n → ℂ) = Δ.1.indicator fun _ => (1 : ℂ) := rfl
    rw [h1, integral_indicator_const _ Δ.2, Complex.real_smul, mul_one]
  refine eq_zero_of_norm_le_mul_forall_pos (M := ∑ j, ‖p.coeff j‖)
    (Finset.sum_nonneg fun _ _ => norm_nonneg _) fun e he => ?_
  obtain ⟨g, hgs, hle, hgc, hgi⟩ := hf.exists_hasCompactSupport_integral_sub_le he
  have hg0 : p.integral g = 0 := by
    rw [← hi]
    exact h0 g (boundedlySupported_of_hasCompactSupport hgc hgs)
  have hj : ∀ j, p.component j ≤ Measure.sum p.component := fun j => Measure.le_sum _ j
  have hsplit : p.integral (Δ.1.indicator 1) =
      ∑ j, p.coeff j * ∫ y, (Δ.1.indicator (1 : Space n → ℂ) y - g y) ∂(p.component j) := by
    have h1 : p.integral (Δ.1.indicator 1) = p.integral (Δ.1.indicator 1) - p.integral g := by
      rw [hg0, sub_zero]
    rw [h1]
    unfold MeasureCombination.integral
    rw [← Finset.sum_sub_distrib]
    refine Finset.sum_congr rfl fun j _ => ?_
    rw [integral_sub (hf.mono_measure (hj j)) (hgi.mono_measure (hj j)), mul_sub]
  rw [hval, hsplit, Finset.sum_mul]
  refine (norm_sum_le _ _).trans (Finset.sum_le_sum fun j _ => ?_)
  rw [norm_mul]
  refine mul_le_mul_of_nonneg_left ?_ (norm_nonneg _)
  refine (norm_integral_le_integral_norm _).trans (le_trans ?_ hle)
  exact integral_mono_measure (hj j) (Eventually.of_forall fun _ => norm_nonneg _)
    (hf.sub hgi).norm
theorem isZeroMeasure_of_fourier_eq_zero {ν : BorelSubset n → ℂ}
    (hν : IsFiniteCombinationMeasure ν)
    (h0 : ∀ v, fourierOfMeasure ν v = 0) : IsZeroMeasure ν := by
  refine isZeroMeasure_of_integral_boundedlySupported hν fun h' hh => ?_
  obtain ⟨p, _, hi⟩ := exists_measureCombination hν
  obtain ⟨S, hS0, hS⟩ := exists_norm_bound_of_boundedlySupported hh
  have hbd : ∀ ε : ℝ, 0 < ε → ∀ y, ‖heatKernelConv h' ε y - h' y‖ ≤ 2 * S := by
    intro ε hε y
    refine (norm_sub_le _ _).trans ?_
    linarith [norm_heatKernelConv_le_of_bound hh hε hS y, hS y]
  have hkey : ∀ ε : ℝ, 0 < ε →
      ‖complexIntegral ν h'‖ ≤ totalMass p * ⨆ y, ‖heatKernelConv h' ε y - h' y‖ := by
    intro ε hε
    have hc : complexIntegral ν (heatKernelConv h' ε) = 0 := by
      rw [integralOfMollified_holds hν hh hε]
      simp [h0]
    rw [hi] at hc
    have hb1 : IsBoundedMeasurableFn h' := isBoundedMeasurableFn_of_continuous hh.1 hS
    have hb2 : IsBoundedMeasurableFn (heatKernelConv h' ε) :=
      isBoundedMeasurableFn_of_continuous (continuous_heatKernelConv hh hε)
        (norm_heatKernelConv_le_of_bound hh hε hS)
    have hd : complexIntegral ν h' = p.integral fun y => h' y - heatKernelConv h' ε y := by
      rw [combination_integral_sub p hb1 hb2, hc, sub_zero, hi]
    rw [hd]
    refine norm_combination_integral_le p fun y => ?_
    rw [norm_sub_rev]
    exact le_ciSup (bddAbove_range_norm_of_le (f := fun y =>
      heatKernelConv h' ε y - h' y) (hbd ε hε)) y
  have hlim := (tendsto_iSup_norm_heatKernelConv_sub hh).const_mul (totalMass p)
  rw [mul_zero] at hlim
  have hle : ‖complexIntegral ν h'‖ ≤ 0 := by
    refine ge_of_tendsto hlim ?_
    filter_upwards [self_mem_nhdsWithin] with ε hε using hkey ε hε
  exact norm_le_zero_iff.1 hle
theorem norm_coords_complex (y : Space 2) :
    ‖(y 0 : ℂ) + Complex.I * (y 1 : ℂ)‖ = ‖y‖ := by
  rw [mul_comm, Complex.norm_add_mul_I, EuclideanSpace.norm_eq]
  simp [Fin.sum_univ_two]
def addCirclePoint (x : UnitAddCircle) : Space 2 :=
  WithLp.toLp 2 ![((AddCircle.toCircle x : Circle) : ℂ).re, ((AddCircle.toCircle x : Circle) : ℂ).im]
theorem continuous_addCirclePoint : Continuous addCirclePoint := by
  unfold addCirclePoint
  refine (PiLp.continuous_toLp 2 _).comp (continuous_pi fun i => ?_)
  have hc : Continuous fun x : UnitAddCircle => ((AddCircle.toCircle x : Circle) : ℂ) :=
    continuous_induced_dom.comp AddCircle.continuous_toCircle
  fin_cases i
  · exact Complex.continuous_re.comp hc
  · exact Complex.continuous_im.comp hc
theorem coords_addCirclePoint (x : UnitAddCircle) :
    ((addCirclePoint x 0 : ℝ) : ℂ) + Complex.I * ((addCirclePoint x 1 : ℝ) : ℂ) =
      ((AddCircle.toCircle x : Circle) : ℂ) := by
  have h0 : addCirclePoint x 0 = ((AddCircle.toCircle x : Circle) : ℂ).re := rfl
  have h1 : addCirclePoint x 1 = ((AddCircle.toCircle x : Circle) : ℂ).im := rfl
  rw [h0, h1, mul_comm]
  exact Complex.re_add_im _
theorem addCirclePoint_mem (x : UnitAddCircle) : addCirclePoint x ∈ planeUnitCircle := by
  show ‖addCirclePoint x‖ = 1
  rw [← norm_coords_complex, coords_addCirclePoint, Circle.norm_coe]
theorem exists_addCirclePoint_eq {y : Space 2} (hy : y ∈ planeUnitCircle) :
    ∃ x, addCirclePoint x = y := by
  have hz : ‖(y 0 : ℂ) + Complex.I * (y 1 : ℂ)‖ = 1 := by
    rw [norm_coords_complex]
    exact hy
  obtain ⟨x, hx⟩ := (AddCircle.homeomorphCircle (T := 1) one_ne_zero).surjective
    (Circle.exp (Complex.arg ((y 0 : ℂ) + Complex.I * (y 1 : ℂ))))
  rw [AddCircle.homeomorphCircle_apply] at hx
  have hc : ((AddCircle.toCircle x : Circle) : ℂ) = (y 0 : ℂ) + Complex.I * (y 1 : ℂ) := by
    rw [hx, Circle.coe_exp]
    have := Complex.norm_mul_exp_arg_mul_I ((y 0 : ℂ) + Complex.I * (y 1 : ℂ))
    rw [hz] at this
    simpa using this
  refine ⟨x, ?_⟩
  ext i
  fin_cases i
  · show ((AddCircle.toCircle x : Circle) : ℂ).re = y 0
    rw [hc]
    simp
  · show ((AddCircle.toCircle x : Circle) : ℂ).im = y 1
    rw [hc]
    simp
theorem circleChar_addCirclePoint (k : ℤ) (x : UnitAddCircle) :
    circleChar k (addCirclePoint x) = fourier k x := by
  unfold circleChar
  rw [Set.indicator_of_mem (addCirclePoint_mem x), coords_addCirclePoint, fourier_apply,
    AddCircle.toCircle_zsmul, Circle.coe_zpow]
theorem isBoundedMeasurableFn_circleChar (k : ℤ) : IsBoundedMeasurableFn (circleChar k) := by
  refine ⟨?_, 1, fun y => ?_⟩
  · refine Measurable.indicator ?_ planeUnitCircleBorel.2
    have h0 : Measurable fun y : Space 2 => (y 0 : ℂ) + Complex.I * (y 1 : ℂ) :=
      (by fun_prop : Continuous fun y : Space 2 => (y 0 : ℂ) + Complex.I * (y 1 : ℂ)).measurable
    exact h0.pow_const k
  · by_cases hy : y ∈ planeUnitCircle
    · unfold circleChar
      rw [Set.indicator_of_mem hy, norm_zpow, norm_coords_complex,
        show ‖y‖ = 1 from hy, one_zpow]
    · unfold circleChar
      rw [Set.indicator_of_notMem hy, norm_zero]
      exact zero_le_one
theorem isBoundedMeasurableFn_add {f g : Space n → ℂ} (hf : IsBoundedMeasurableFn f)
    (hg : IsBoundedMeasurableFn g) : IsBoundedMeasurableFn fun y => f y + g y := by apply _root_.YangMills.Construction.EuclideanBorel.FunctionalCalculus.boundedFn_add <;> assumption
theorem isBoundedMeasurableFn_const_mul (a : ℂ) {f : Space n → ℂ}
    (hf : IsBoundedMeasurableFn f) : IsBoundedMeasurableFn fun y => a * f y := by
  obtain ⟨hfm, C, hC⟩ := hf
  refine ⟨hfm.const_mul a, ‖a‖ * C, fun y => ?_⟩
  rw [norm_mul]
  exact mul_le_mul_of_nonneg_left (hC y) (norm_nonneg _)
theorem exists_planeLift_of_span_fourier (p : MeasureCombination 2)
    (h0 : ∀ k, p.integral (circleChar k) = 0)
    (F : C(UnitAddCircle, ℂ))
    (hF : F ∈ Submodule.span ℂ (Set.range (fourier (T := 1)))) :
    ∃ G : Space 2 → ℂ, IsBoundedMeasurableFn G ∧ (∀ x, F x = G (addCirclePoint x)) ∧
      (∀ y, y ∉ planeUnitCircle → G y = 0) ∧ p.integral G = 0 := by
  induction hF using Submodule.span_induction with
  | mem F hF =>
    obtain ⟨k, rfl⟩ := hF
    exact ⟨circleChar k, isBoundedMeasurableFn_circleChar k,
      fun x => (circleChar_addCirclePoint k x).symm,
      fun y hy => Set.indicator_of_notMem hy _, h0 k⟩
  | zero =>
    refine ⟨fun _ => 0, ⟨measurable_const, 0, fun _ => by simp⟩, fun _ => rfl, fun _ _ => rfl, ?_⟩
    simp [MeasureCombination.integral]
  | add F₁ F₂ _ _ ih₁ ih₂ =>
    obtain ⟨G₁, hb₁, hx₁, hz₁, hi₁⟩ := ih₁
    obtain ⟨G₂, hb₂, hx₂, hz₂, hi₂⟩ := ih₂
    refine ⟨fun y => G₁ y + G₂ y, isBoundedMeasurableFn_add hb₁ hb₂, fun x => ?_,
      fun y hy => ?_, ?_⟩
    · simp [hx₁ x, hx₂ x]
    · simp [hz₁ y hy, hz₂ y hy]
    · rw [combination_integral_add p hb₁ hb₂, hi₁, hi₂, add_zero]
  | smul a F _ ih =>
    obtain ⟨G, hb, hx, hz, hi⟩ := ih
    refine ⟨fun y => a * G y, isBoundedMeasurableFn_const_mul a hb, fun x => ?_,
      fun y hy => ?_, ?_⟩
    · simp [hx x]
    · simp [hz y hy]
    · rw [combination_integral_const_mul, hi, mul_zero]
theorem isZeroMeasure_of_circleChar (hR : WeightedMeasureTheorem)
    {ν : BorelSubset 2 → ℂ} (hν : IsFiniteCombinationMeasure ν)
    (hX : IsSupportedOn ν planeUnitCircleBorel)
    (h0 : ∀ k : ℤ, complexIntegral ν (circleChar k) = 0) : IsZeroMeasure ν := by
  refine isZeroMeasure_of_integral_boundedlySupported hν fun h' hh => ?_
  obtain ⟨p, _, hi⟩ := exists_measureCombination hν
  obtain ⟨S, hS0, hS⟩ := exists_norm_bound_of_boundedlySupported hh
  have hb := isBoundedMeasurableFn_of_continuous hh.1 hS
  rw [(hR 2 (by norm_num) ν hν planeUnitCircleBorel h' h' hb hb).2.1 hX, hi]
  have hp0 : ∀ k, p.integral (circleChar k) = 0 := fun k => by
    rw [← hi]
    exact h0 k
  set f : Space 2 → ℂ := h' * planeUnitCircleBorel.1.indicator 1 with hfdef
  have hfon : ∀ y, y ∈ planeUnitCircle → f y = h' y := by
    intro y hy
    have : y ∈ planeUnitCircleBorel.1 := hy
    simp [hfdef, Set.indicator_of_mem this]
  have hfoff : ∀ y, y ∉ planeUnitCircle → f y = 0 := by
    intro y hy
    have : y ∉ planeUnitCircleBorel.1 := hy
    simp [hfdef, Set.indicator_of_notMem this]
  have hfb : IsBoundedMeasurableFn f := by
    refine ⟨hh.1.measurable.mul (measurable_one.indicator planeUnitCircleBorel.2), S, fun y => ?_⟩
    by_cases hy : y ∈ planeUnitCircle
    · rw [hfon y hy]
      exact hS y
    · rw [hfoff y hy, norm_zero]
      exact hS0
  refine eq_zero_of_norm_le_mul_forall_pos (totalMass_nonneg p) fun e he => ?_
  let F₀ : C(UnitAddCircle, ℂ) := ⟨fun x => h' (addCirclePoint x), hh.1.comp continuous_addCirclePoint⟩
  have hcl : F₀ ∈ closure
      ((Submodule.span ℂ (Set.range (fourier (T := 1))) : Submodule ℂ C(UnitAddCircle, ℂ)) :
        Set C(UnitAddCircle, ℂ)) := by
    rw [← Submodule.topologicalClosure_coe, span_fourier_closure_eq_top]
    trivial
  obtain ⟨F, hFs, hFd⟩ := Metric.mem_closure_iff.1 hcl e he
  obtain ⟨G, hGb, hGF, hGz, hG0⟩ := exists_planeLift_of_span_fourier p hp0 F hFs
  have hd : p.integral f = p.integral fun y => f y - G y := by
    rw [combination_integral_sub p hfb hGb, hG0, sub_zero]
  rw [hd]
  refine norm_combination_integral_le p fun y => ?_
  by_cases hy : y ∈ planeUnitCircle
  · obtain ⟨x, rfl⟩ := exists_addCirclePoint_eq hy
    rw [hfon _ hy, ← hGF x, ← dist_eq_norm]
    exact (ContinuousMap.dist_apply_le_dist x).trans hFd.le
  · rw [hfoff y hy, hGz y hy, sub_zero, norm_zero]
    exact he.le
theorem determiningFamilies (hR : WeightedMeasureTheorem) : DeterminingFamiliesStatement := by
  refine ⟨fun n _ => ⟨fun ε hε => gaussianFourierIdentities_holds hε, fun h hh => ⟨fun ε hε => ⟨?_,
    mollifiedFourierIdentities_holds hh hε⟩, tendsto_iSup_norm_heatKernelConv_sub hh,
    fourierOfFnProperties_holds hh⟩,
    fun ν hν => ⟨fourierOfMeasureProperties_holds hν,
      fun h hh ε hε => integralOfMollified_holds hν hh hε,
      isZeroMeasure_of_integral_boundedlySupported hν, isZeroMeasure_of_fourier_eq_zero hν⟩⟩,
    fun ν hν hX h0 => isZeroMeasure_of_circleChar hR hν hX h0⟩
  obtain ⟨S, _, hS⟩ := exists_norm_bound_of_boundedlySupported hh
  exact ⟨continuous_heatKernelConv hh hε, tendsto_heatKernelConv_atInfty hh hε,
    norm_heatKernelConv_le_of_bound hh hε fun y => le_ciSup (bddAbove_range_norm_of_le hS) y,
    integrable_heatKernelConv hh hε, integral_norm_heatKernelConv_le hh hε,
    fun hpos y => heatKernelConv_real_nonneg hε hpos y⟩
end YangMills.Construction.EuclideanBorel.MeasureUniqueness
