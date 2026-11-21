import YangMills.Construction.SpectralMeasures.UniquenessOfComplexMeasures
import YangMills.Construction.SpectralMeasures.ScalarMeasuresOfAUnitaryRepresentation
import Mathlib
set_option autoImplicit false
open MeasureTheory Filter Topology
open scoped InnerProductSpace ComplexConjugate FourierTransform
noncomputable section
namespace YangMills.Construction.EuclideanBorel
open YangMills.Construction.FormsOperators (IsStronglyContUnitaryRep UnitaryMap)
namespace ScalarMeasures
section Gaussian
variable {n : ℕ}
def gaussianWeight (b : ℝ) (v : Space n) : ℝ := Real.exp (-b * ‖v‖ ^ 2)
theorem gaussianWeight_pos (b : ℝ) (v : Space n) : 0 < gaussianWeight b v := Real.exp_pos _
theorem continuous_gaussianWeight (b : ℝ) : Continuous (gaussianWeight b : Space n → ℝ) := by
  unfold gaussianWeight
  fun_prop
theorem integrable_gaussianWeight {b : ℝ} (hb : 0 < b) :
    Integrable (gaussianWeight b : Space n → ℝ) := by apply _root_.YangMills.Construction.EuclideanBorel.MeasureUniqueness.integrable_exp_neg_mul_normSq <;> assumption
theorem integral_gaussianWeight_pos {b : ℝ} (hb : 0 < b) :
    0 < ∫ v, gaussianWeight b (v : Space n) := by
  have := GaussianFourier.integral_rexp_neg_mul_sq_norm (V := Space n) hb
  unfold gaussianWeight
  rw [this]
  have : 0 < Real.pi / b := div_pos Real.pi_pos hb
  positivity
theorem gaussianWeight_mul_gaussianWeight (b : ℝ) (v s : Space n) :
    gaussianWeight (2 * b) v * gaussianWeight (2 * b) (v + s) =
      gaussianWeight (4 * b) (v + (1 / 2 : ℝ) • s) * gaussianWeight b s := by
  simp only [gaussianWeight, ← Real.exp_add]
  congr 1
  have h1 := norm_add_sq_real v s
  have h2 := norm_add_sq_real v ((1 / 2 : ℝ) • s)
  rw [inner_smul_right, norm_smul] at h2
  simp only [Real.norm_eq_abs, abs_of_pos (by norm_num : (0 : ℝ) < 1 / 2)] at h2
  rw [h1, h2]
  ring
end Gaussian
section Transform
variable {n : ℕ}
def planeWave (w v : Space n) : ℂ :=
  Complex.exp (((-2 * Real.pi * inner ℝ v w : ℝ) : ℂ) * Complex.I)
theorem continuous_planeWave (w : Space n) : Continuous (planeWave w) := by
  unfold planeWave
  fun_prop
theorem norm_planeWave (w v : Space n) : ‖planeWave w v‖ = 1 :=
  Complex.norm_exp_ofReal_mul_I _
theorem planeWave_add (w v s : Space n) :
    planeWave w (v + s) = planeWave w v * planeWave w s := by
  simp only [planeWave, inner_add_left, mul_add, Complex.ofReal_add, add_mul, Complex.exp_add]
theorem conj_planeWave_mul (w v : Space n) : conj (planeWave w v) * planeWave w v = 1 := by
  rw [mul_comm, Complex.mul_conj, Complex.normSq_eq_norm_sq, norm_planeWave]
  simp
theorem fourier_eq_integral_planeWave (f : Space n → ℂ) (w : Space n) :
    𝓕 f w = ∫ v, planeWave w v * f v := by
  rw [Real.fourier_eq']
  rfl
theorem integrable_fourier_of_real_nonneg {f : Space n → ℂ} (hf : Integrable f)
    (hc : Continuous f) (hpos : ∀ w, ∃ r : ℝ, 0 ≤ r ∧ 𝓕 f w = r) : Integrable (𝓕 f) := by
  have hcont : Continuous (𝓕 f) :=
    VectorFourier.fourierIntegral_continuous Real.continuous_fourierChar
      (by exact continuous_inner) hf
  set G : Space n → ℝ := fun w => (𝓕 f w).re with hG
  have hGc : Continuous G := Complex.continuous_re.comp hcont
  have hGf : ∀ w, 𝓕 f w = (G w : ℂ) := fun w => by
    obtain ⟨r, -, hr⟩ := hpos w
    simp [hG, hr]
  have hG0 : ∀ w, 0 ≤ G w := fun w => by
    obtain ⟨r, h0, hr⟩ := hpos w
    simpa [hG, hr] using h0
  have hbd : ∀ w, G w ≤ ∫ v, ‖f v‖ := fun w => by
    have h1 : ‖𝓕 f w‖ ≤ ∫ v, ‖f v‖ := by
      rw [fourier_eq_integral_planeWave]
      calc ‖∫ v, planeWave w v * f v‖ ≤ ∫ v, ‖planeWave w v * f v‖ := norm_integral_le_integral_norm _
        _ = ∫ v, ‖f v‖ := by simp [norm_planeWave]
    rw [hGf, Complex.norm_real, Real.norm_of_nonneg (hG0 w)] at h1
    exact h1
  have hT : Tendsto (fun c : ℝ => ∫ w, ((gaussianWeight c⁻¹ w * G w : ℝ) : ℂ)) atTop (𝓝 (f 0)) := by
    refine (Real.tendsto_integral_gaussian_smul' hf hc.continuousAt (v := 0)).congr' ?_
    filter_upwards [Ioi_mem_atTop 0] with c (hc0 : 0 < c)
    have J : Integrable (fun w : Space n => Complex.exp (-(c : ℂ)⁻¹ * ‖w‖ ^ 2 +
        2 * Real.pi * Complex.I * (inner ℝ (0 : Space n) w : ℝ))) :=
      GaussianFourier.integrable_cexp_neg_mul_sq_norm_add (by simpa using hc0) _ _
    have key : ∫ w, Complex.exp (-(c : ℂ)⁻¹ * ‖w‖ ^ 2 +
          2 * Real.pi * Complex.I * (inner ℝ (0 : Space n) w : ℝ)) • 𝓕 f w =
        ∫ w, 𝓕 (fun w : Space n => Complex.exp (-(c : ℂ)⁻¹ * ‖w‖ ^ 2 +
          2 * Real.pi * Complex.I * (inner ℝ (0 : Space n) w : ℝ))) w • f w := by
      simpa using! (VectorFourier.integral_fourierIntegral_smul_eq_flip (L := innerₗ (Space n))
        Real.continuous_fourierChar (by exact continuous_inner) J hf).symm
    have hL : ∫ w, ((gaussianWeight c⁻¹ w * G w : ℝ) : ℂ) =
        ∫ w, Complex.exp (-(c : ℂ)⁻¹ * ‖w‖ ^ 2 +
          2 * Real.pi * Complex.I * (inner ℝ (0 : Space n) w : ℝ)) • 𝓕 f w := by
      refine integral_congr_ae (ae_of_all _ fun w => ?_)
      simp only [inner_zero_left, gaussianWeight, hGf w, smul_eq_mul]
      push_cast
      simp
    rw [hL, key]
    refine integral_congr_ae (ae_of_all _ fun w => ?_)
    simp only []
    rw [fourier_gaussian_innerProductSpace' (by simpa using hc0)]
    have e1 : (Real.pi : ℂ) / (c : ℂ)⁻¹ = (Real.pi : ℂ) * c := by
      rw [div_inv_eq_mul]
    have e2 : -(Real.pi : ℂ) ^ 2 * ‖(0 : Space n) - w‖ ^ 2 / (c : ℂ)⁻¹ =
        -(Real.pi : ℂ) ^ 2 * c * ‖(0 : Space n) - w‖ ^ 2 := by
      rw [div_inv_eq_mul]
      ring
    rw [e1, e2]
  have hmeanInt : ∀ c : ℝ, 0 < c → Integrable (fun w => gaussianWeight c⁻¹ w * G w) := fun c hc0 =>
    ((integrable_gaussianWeight (inv_pos.mpr hc0)).mul_const (∫ v, ‖f v‖)).mono'
      ((continuous_gaussianWeight _).mul hGc).aestronglyMeasurable
      (ae_of_all _ fun w => by
        rw [Real.norm_of_nonneg (mul_nonneg (gaussianWeight_pos _ _).le (hG0 w))]
        exact mul_le_mul_of_nonneg_left (hbd w) (gaussianWeight_pos _ _).le)
  have hL : ∀ c : ℝ, 0 < c → ∫⁻ w, ENNReal.ofReal (gaussianWeight c⁻¹ w * G w) =
      ENNReal.ofReal (∫ w, gaussianWeight c⁻¹ w * G w) := fun c hc0 =>
    (ofReal_integral_eq_lintegral_ofReal (hmeanInt c hc0)
      (ae_of_all _ fun w => mul_nonneg (gaussianWeight_pos _ _).le (hG0 w))).symm
  have hT' : Tendsto (fun c : ℝ => ∫ w, gaussianWeight c⁻¹ w * G w) atTop (𝓝 (f 0).re) := by
    refine ((Complex.continuous_re.tendsto _).comp hT).congr fun c => ?_
    simp only [Function.comp]
    rw [integral_complex_ofReal, Complex.ofReal_re]
  have hfin : ∫⁻ w, ENNReal.ofReal (G w) < ⊤ := by
    set cs : ℕ → ℝ := fun k => (k : ℝ) + 1 with hcsdef
    have hcs : Tendsto cs atTop atTop :=
      tendsto_atTop_add_const_right _ _ tendsto_natCast_atTop_atTop
    have hcs0 : ∀ k, 0 < cs k := fun k => by positivity
    have hpt : ∀ w, Tendsto (fun k => ENNReal.ofReal (gaussianWeight (cs k)⁻¹ w * G w)) atTop
        (𝓝 (ENNReal.ofReal (G w))) := fun w => by
      refine ENNReal.tendsto_ofReal ?_
      have h2 : Tendsto (fun k => (cs k)⁻¹) atTop (𝓝 0) := tendsto_inv_atTop_zero.comp hcs
      have h3 : Continuous fun b : ℝ => gaussianWeight b w := by
        unfold gaussianWeight
        fun_prop
      have h1 : Tendsto (fun k => gaussianWeight (cs k)⁻¹ w) atTop (𝓝 1) := by
        have h4 := (h3.tendsto 0).comp h2
        have h5 : gaussianWeight 0 w = 1 := by simp [gaussianWeight]
        rw [h5] at h4
        exact h4
      simpa using h1.mul_const (G w)
    calc ∫⁻ w, ENNReal.ofReal (G w)
        = ∫⁻ w, liminf (fun k => ENNReal.ofReal (gaussianWeight (cs k)⁻¹ w * G w)) atTop :=
          lintegral_congr fun w => (hpt w).liminf_eq.symm
      _ ≤ liminf (fun k => ∫⁻ w, ENNReal.ofReal (gaussianWeight (cs k)⁻¹ w * G w)) atTop :=
          lintegral_liminf_le fun k =>
            ENNReal.measurable_ofReal.comp ((continuous_gaussianWeight _).mul hGc).measurable
      _ = ENNReal.ofReal (f 0).re := by
          refine Tendsto.liminf_eq ?_
          exact ((ENNReal.tendsto_ofReal (hT'.comp hcs))).congr fun k => (hL _ (hcs0 k)).symm
      _ < ⊤ := ENNReal.ofReal_lt_top
  have hGi : Integrable G :=
    ⟨hGc.aestronglyMeasurable, (hasFiniteIntegral_iff_ofReal (ae_of_all _ hG0)).2 hfin⟩
  exact hGi.ofReal.congr (ae_of_all _ fun w => (hGf w).symm)
end Transform
section Representation
variable {H : Type} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H] {n : ℕ}
def matrixCoeff (V : Space n → UnitaryMap H H) (ψ : H) (v : Space n) : ℂ :=
  ⟪ψ, V v ψ⟫_ℂ
def dampedCoeff (V : Space n → UnitaryMap H H) (ψ : H) (b : ℝ) (v : Space n) : ℂ :=
  matrixCoeff V ψ v * (gaussianWeight b v : ℂ)
variable {V : Space n → UnitaryMap H H}
omit [CompleteSpace H] in
theorem continuous_matrixCoeff (hV : IsStronglyContUnitaryRep V) (ψ : H) :
    Continuous (matrixCoeff V ψ) :=
  continuous_const.inner (hV.continuous_apply ψ)
omit [CompleteSpace H] in
theorem norm_matrixCoeff_le (ψ : H) (v : Space n) : ‖matrixCoeff V ψ v‖ ≤ ‖ψ‖ ^ 2 := by
  calc ‖matrixCoeff V ψ v‖ ≤ ‖ψ‖ * ‖V v ψ‖ := norm_inner_le_norm _ _
    _ = ‖ψ‖ ^ 2 := by
      rw [(V v).norm_map]
      ring
omit [CompleteSpace H] in
theorem inner_map_translate (hV : IsStronglyContUnitaryRep V) (ψ : H)
    (v s : Space n) : ⟪V v ψ, V (v + s) ψ⟫_ℂ = matrixCoeff V ψ s := by
  rw [← hV.map_add]
  exact (V v).inner_map_map ψ (V s ψ)
omit [CompleteSpace H] in
theorem continuous_dampedCoeff (hV : IsStronglyContUnitaryRep V) (ψ : H) (b : ℝ) :
    Continuous (dampedCoeff V ψ b) :=
  (continuous_matrixCoeff hV ψ).mul (Complex.continuous_ofReal.comp (continuous_gaussianWeight b))
theorem integrable_dampedCoeff (hV : IsStronglyContUnitaryRep V) (ψ : H) {b : ℝ}
    (hb : 0 < b) : Integrable (dampedCoeff V ψ b) :=
  ((integrable_gaussianWeight hb).const_mul (‖ψ‖ ^ 2)).mono'
    (continuous_dampedCoeff hV ψ b).aestronglyMeasurable (ae_of_all _ fun v => by
      simp only [dampedCoeff, norm_mul, Complex.norm_real,
        Real.norm_of_nonneg (gaussianWeight_pos b v).le]
      exact mul_le_mul_of_nonneg_right (norm_matrixCoeff_le ψ v) (gaussianWeight_pos b v).le)
theorem fourier_dampedCoeff_nonneg (hV : IsStronglyContUnitaryRep V) (ψ : H)
    {b : ℝ} (hb : 0 < b) (w : Space n) :
    ∃ r : ℝ, 0 ≤ r ∧ 𝓕 (dampedCoeff V ψ b) w = r := by
  have hg : Integrable (gaussianWeight (2 * b) : Space n → ℝ) :=
    integrable_gaussianWeight (by positivity)
  set g : Space n → ℝ := gaussianWeight (2 * b) with hgdef
  have hgc : Continuous g := continuous_gaussianWeight _
  have hg0 : ∀ v, 0 < g v := gaussianWeight_pos _
  set h : Space n → H := fun v => (planeWave w v * (g v : ℂ)) • V v ψ with hdef
  have hhc : Continuous h :=
    ((continuous_planeWave w).mul (Complex.continuous_ofReal.comp hgc)).smul
      (hV.continuous_apply ψ)
  have hhi : Integrable h := (hg.mul_const ‖ψ‖).mono' hhc.aestronglyMeasurable
    (ae_of_all _ fun v => by
      simp only [hdef, norm_smul, norm_mul, norm_planeWave, Complex.norm_real,
        Real.norm_of_nonneg (hg0 v).le, one_mul, (V v).norm_map]
      exact le_rfl)
  set x : H := ∫ v, h v with hx
  have hR : ∀ v s, ⟪h v, h (v + s)⟫_ℂ =
      planeWave w s * matrixCoeff V ψ s * ((g v * g (v + s) : ℝ) : ℂ) := by
    intro v s
    have h1 := conj_planeWave_mul w v
    simp only [hdef, inner_smul_left, inner_smul_right, inner_map_translate hV, planeWave_add,
      map_mul, Complex.conj_ofReal]
    push_cast
    linear_combination (planeWave w s * matrixCoeff V ψ s * (g v : ℂ) * (g (v + s) : ℂ)) * h1
  have hRc : Continuous fun p : Space n × Space n => ⟪h p.1, h (p.1 + p.2)⟫_ℂ :=
    (hhc.comp continuous_fst).inner (hhc.comp (continuous_fst.add continuous_snd))
  have hRi : Integrable (fun p : Space n × Space n => ⟪h p.1, h (p.1 + p.2)⟫_ℂ)
      (volume.prod volume) := by
    have h1 : Integrable (fun p : Space n × Space n => g p.1 * g p.2)
        (volume.prod volume) := hg.mul_prod hg
    have h2 : Integrable (fun p : Space n × Space n => g p.1 * g (p.1 + p.2))
        (volume.prod volume) :=
      (measurePreserving_prod_add volume volume).integrable_comp_of_integrable h1
    refine (h2.const_mul (‖ψ‖ ^ 2)).mono' hRc.aestronglyMeasurable (ae_of_all _ fun p => ?_)
    rw [hR, norm_mul, norm_mul, norm_planeWave, one_mul, Complex.norm_real,
      Real.norm_of_nonneg (mul_pos (hg0 _) (hg0 _)).le]
    exact mul_le_mul_of_nonneg_right (norm_matrixCoeff_le ψ p.2) (mul_pos (hg0 _) (hg0 _)).le
  have hxx : ((‖x‖ ^ 2 : ℝ) : ℂ) = ∫ v, ∫ s, ⟪h v, h (v + s)⟫_ℂ := by
    have h1 : ∀ v, ⟪h v, x⟫_ℂ = ∫ s, ⟪h v, h (v + s)⟫_ℂ := fun v => by
      rw [hx, ← integral_inner hhi]
      exact (integral_add_left_eq_self (fun y => ⟪h v, h y⟫_ℂ) v).symm
    have h2 : ⟪x, x⟫_ℂ = ∫ v, ⟪h v, x⟫_ℂ := by
      have h3 : ∫ v, ⟪h v, x⟫_ℂ = ∫ v, conj ⟪x, h v⟫_ℂ := by
        simp only [inner_conj_symm]
      rw [h3, integral_conj, integral_inner hhi, inner_conj_symm]
    have h4 : ((‖x‖ ^ 2 : ℝ) : ℂ) = ⟪x, x⟫_ℂ := by
      rw [inner_self_eq_norm_sq_to_K]
      simp
    rw [h4, h2]
    exact integral_congr_ae (ae_of_all _ h1)
  set C : ℝ := ∫ v, gaussianWeight (4 * b) (v : Space n) with hCdef
  have hC0 : 0 < C := integral_gaussianWeight_pos (by positivity)
  have hC : ∀ s, ∫ v, g v * g (v + s) = C * gaussianWeight b s := fun s => by
    simp only [hgdef, gaussianWeight_mul_gaussianWeight]
    rw [integral_mul_const, integral_add_right_eq_self (gaussianWeight (4 * b)) ((1 / 2 : ℝ) • s)]
  have hswap : ∫ v, ∫ s, ⟪h v, h (v + s)⟫_ℂ = ∫ s, ∫ v, ⟪h v, h (v + s)⟫_ℂ :=
    integral_integral_swap (f := fun v s => ⟪h v, h (v + s)⟫_ℂ) hRi
  have hinner : ∀ s, ∫ v, ⟪h v, h (v + s)⟫_ℂ =
      (C : ℂ) * (planeWave w s * dampedCoeff V ψ b s) := fun s => by
    simp only [hR]
    rw [integral_const_mul, integral_complex_ofReal, hC]
    simp only [dampedCoeff]
    push_cast
    ring
  have hfinal : ((‖x‖ ^ 2 : ℝ) : ℂ) = (C : ℂ) * 𝓕 (dampedCoeff V ψ b) w := by
    rw [hxx, hswap, fourier_eq_integral_planeWave, ← integral_const_mul]
    exact integral_congr_ae (ae_of_all _ hinner)
  refine ⟨‖x‖ ^ 2 / C, by positivity, ?_⟩
  have hCne : (C : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr hC0.ne'
  push_cast at hfinal ⊢
  field_simp
  rw [hfinal]
  ring
def spectralDensity (V : Space n → UnitaryMap H H) (ψ : H) (b : ℝ) (w : Space n) : ℝ :=
  (𝓕 (dampedCoeff V ψ b) w).re
theorem fourier_dampedCoeff_eq (hV : IsStronglyContUnitaryRep V) (ψ : H) {b : ℝ}
    (hb : 0 < b) (w : Space n) : 𝓕 (dampedCoeff V ψ b) w = (spectralDensity V ψ b w : ℂ) := by
  obtain ⟨r, -, hr⟩ := fourier_dampedCoeff_nonneg hV ψ hb w
  simp [spectralDensity, hr]
theorem spectralDensity_nonneg (hV : IsStronglyContUnitaryRep V) (ψ : H) {b : ℝ}
    (hb : 0 < b) (w : Space n) : 0 ≤ spectralDensity V ψ b w := by
  obtain ⟨r, h0, hr⟩ := fourier_dampedCoeff_nonneg hV ψ hb w
  simpa [spectralDensity, hr] using h0
theorem integrable_fourier_dampedCoeff (hV : IsStronglyContUnitaryRep V) (ψ : H)
    {b : ℝ} (hb : 0 < b) : Integrable (𝓕 (dampedCoeff V ψ b)) :=
  integrable_fourier_of_real_nonneg (integrable_dampedCoeff hV ψ hb) (continuous_dampedCoeff hV ψ b)
    (fourier_dampedCoeff_nonneg hV ψ hb)
theorem continuous_spectralDensity (hV : IsStronglyContUnitaryRep V) (ψ : H) {b : ℝ}
    (hb : 0 < b) : Continuous (spectralDensity V ψ b) :=
  Complex.continuous_re.comp (VectorFourier.fourierIntegral_continuous Real.continuous_fourierChar
    (by exact continuous_inner) (integrable_dampedCoeff hV ψ hb))
def smoothedMeasure (V : Space n → UnitaryMap H H) (ψ : H) (b : ℝ) : Measure (Space n) :=
  volume.withDensity fun w => ENNReal.ofReal (spectralDensity V ψ b w)
theorem charFun_smoothedMeasure (hV : IsStronglyContUnitaryRep V) (ψ : H) {b : ℝ}
    (hb : 0 < b) (t : Space n) :
    charFun (smoothedMeasure V ψ b) t = dampedCoeff V ψ b ((2 * Real.pi)⁻¹ • t) := by
  have hinv := congrFun ((continuous_dampedCoeff hV ψ b).fourierInv_fourier_eq
    (integrable_dampedCoeff hV ψ hb) (integrable_fourier_dampedCoeff hV ψ hb)) ((2 * Real.pi)⁻¹ • t)
  have hm : Measurable fun w => ENNReal.ofReal (spectralDensity V ψ b w) :=
    ENNReal.measurable_ofReal.comp (continuous_spectralDensity hV ψ hb).measurable
  rw [charFun_apply, smoothedMeasure, integral_withDensity_eq_integral_toReal_smul hm
    (ae_of_all _ fun w => ENNReal.ofReal_lt_top), ← hinv, Real.fourierInv_eq']
  refine integral_congr_ae (ae_of_all _ fun w => ?_)
  simp only []
  rw [ENNReal.toReal_ofReal (spectralDensity_nonneg hV ψ hb w), fourier_dampedCoeff_eq hV ψ hb,
    real_inner_smul_right]
  have e : 2 * Real.pi * ((2 * Real.pi)⁻¹ * inner ℝ w t) = inner ℝ w t := by
    have := Real.pi_ne_zero
    field_simp
  rw [e, Complex.real_smul, smul_eq_mul, mul_comm]
theorem isProbabilityMeasure_smoothedMeasure (hV : IsStronglyContUnitaryRep V) {ψ : H}
    (hψ : ‖ψ‖ = 1) {b : ℝ} (hb : 0 < b) : IsProbabilityMeasure (smoothedMeasure V ψ b) := by
  have h0 := charFun_zero (smoothedMeasure V ψ b)
  rw [charFun_smoothedMeasure hV ψ hb, smul_zero] at h0
  have h1 : dampedCoeff V ψ b 0 = 1 := by
    simp only [dampedCoeff, matrixCoeff, hV.map_zero, gaussianWeight]
    simp [inner_self_eq_norm_sq_to_K, hψ]
  rw [h1] at h0
  have h2 : (smoothedMeasure V ψ b).real Set.univ = 1 := by exact_mod_cast h0.symm
  refine ⟨?_⟩
  rw [Measure.real, ENNReal.toReal_eq_one_iff] at h2
  exact h2
theorem exists_probabilityMeasure_charFun (hV : IsStronglyContUnitaryRep V) {ψ : H}
    (hψ : ‖ψ‖ = 1) : ∃ ρ : ProbabilityMeasure (Space n), ∀ t,
      charFun (ρ : Measure (Space n)) t = matrixCoeff V ψ ((2 * Real.pi)⁻¹ • t) := by
  set bs : ℕ → ℝ := fun k => ((k : ℝ) + 1)⁻¹ with hbsdef
  have hbs : ∀ k, 0 < bs k := fun k => by positivity
  have hbs0 : Tendsto bs atTop (𝓝 0) :=
    tendsto_inv_atTop_zero.comp (tendsto_atTop_add_const_right _ _ tendsto_natCast_atTop_atTop)
  have hprob : ∀ k, IsProbabilityMeasure (smoothedMeasure V ψ (bs k)) := fun k =>
    isProbabilityMeasure_smoothedMeasure hV hψ (hbs k)
  set P : ℕ → ProbabilityMeasure (Space n) := fun k => ⟨smoothedMeasure V ψ (bs k), hprob k⟩ with hP
  set L : Space n → ℂ := fun t => matrixCoeff V ψ ((2 * Real.pi)⁻¹ • t) with hL
  have hLc : Continuous L := (continuous_matrixCoeff hV ψ).comp (continuous_const_smul _)
  have hconv : ∀ t, Tendsto (fun k => charFun (smoothedMeasure V ψ (bs k)) t) atTop (𝓝 (L t)) := by
    intro t
    have hval : (fun k => charFun (smoothedMeasure V ψ (bs k)) t) = fun k =>
        matrixCoeff V ψ ((2 * Real.pi)⁻¹ • t) *
          ((gaussianWeight (bs k) ((2 * Real.pi)⁻¹ • t) : ℝ) : ℂ) :=
      funext fun k => charFun_smoothedMeasure hV ψ (hbs k) t
    rw [hval]
    have h3 : Continuous fun b : ℝ => ((gaussianWeight b ((2 * Real.pi)⁻¹ • t) : ℝ) : ℂ) := by
      unfold gaussianWeight
      fun_prop
    have h4 := (h3.tendsto 0).comp hbs0
    have h5 : ((gaussianWeight 0 ((2 * Real.pi)⁻¹ • t) : ℝ) : ℂ) = 1 := by simp [gaussianWeight]
    rw [h5] at h4
    have h6 := (tendsto_const_nhds (x := matrixCoeff V ψ ((2 * Real.pi)⁻¹ • t))
      (f := (atTop : Filter ℕ))).mul h4
    rw [mul_one] at h6
    exact h6
  have htight : IsTightMeasureSet (Set.range fun k => smoothedMeasure V ψ (bs k)) :=
    @isTightMeasureSet_of_tendsto_charFun _ _ _ _ _ _ (fun k => smoothedMeasure V ψ (bs k)) hprob L
      hLc.continuousAt hconv
  have hS : IsTightMeasureSet
      {((μ : ProbabilityMeasure (Space n)) : Measure (Space n)) | μ ∈ Set.range P} := by
    convert htight using 1
    ext ν
    constructor
    · rintro ⟨_, ⟨k, rfl⟩, rfl⟩
      exact ⟨k, rfl⟩
    · rintro ⟨k, rfl⟩
      exact ⟨P k, ⟨k, rfl⟩, rfl⟩
  have hcomp := isCompact_closure_of_isTightMeasureSet hS
  obtain ⟨ρ, -, hρ⟩ := hcomp.exists_mapClusterPt (f := atTop) (u := P)
    (tendsto_principal.2 (Eventually.of_forall fun k => subset_closure ⟨k, rfl⟩))
  obtain ⟨U, hU, hUt⟩ := mapClusterPt_iff_ultrafilter.1 hρ
  refine ⟨ρ, fun t => ?_⟩
  have h1 : Tendsto (fun k => charFun (P k : Measure (Space n)) t) U
      (𝓝 (charFun (ρ : Measure (Space n)) t)) := by
    rw [ProbabilityMeasure.tendsto_iff_forall_integral_rclike_tendsto ℂ] at hUt
    simp_rw [charFun_eq_integral_innerProbChar]
    exact hUt (BoundedContinuousFunction.innerProbChar t)
  exact tendsto_nhds_unique h1 ((hconv t).mono_left hU)
end Representation
theorem existsFiniteMeasure_holds : ExistsFiniteMeasure := by
  intro H _ _ _ n _ V hV ψ
  by_cases hψ : ψ = 0
  · refine ⟨0, inferInstance, fun v => ?_⟩
    simp [hψ]
  have hnorm : ‖ψ‖ ≠ 0 := norm_ne_zero_iff.mpr hψ
  have hnormC : (‖ψ‖ : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr hnorm
  set ψ' : H := ((‖ψ‖ : ℂ)⁻¹) • ψ with hψ'
  have h1 : ‖ψ'‖ = 1 := by
    rw [hψ', norm_smul, norm_inv, Complex.norm_real, norm_norm, inv_mul_cancel₀ hnorm]
  obtain ⟨ρ, hρ⟩ := exists_probabilityMeasure_charFun hV h1
  set ν : Measure (Space n) :=
    (ρ : Measure (Space n)).map fun y => (2 * Real.pi) • y with hν
  have hνfin : IsFiniteMeasure ν :=
    Measure.isFiniteMeasure_map _ _
  have hchar : ∀ v, charFun ν v = matrixCoeff V ψ' v := fun v => by
    rw [hν, charFun_map_smul, hρ, smul_smul,
      inv_mul_cancel₀ (by positivity : (2 * Real.pi : ℝ) ≠ 0), one_smul]
  have hexp : ∀ v, ∫ y, expChar v y ∂ν = matrixCoeff V ψ' v := fun v => by
    rw [← hchar, charFun_apply]
    refine integral_congr_ae (ae_of_all _ fun y => ?_)
    simp only [expChar]
    rw [real_inner_comm, mul_comm]
  refine ⟨ENNReal.ofReal (‖ψ‖ ^ 2) • ν, Measure.smul_finite _ ENNReal.ofReal_ne_top, fun v => ?_⟩
  rw [integral_smul_measure, hexp, ENNReal.toReal_ofReal (by positivity)]
  simp only [matrixCoeff, hψ', map_smul, inner_smul_left, inner_smul_right, map_inv₀,
    Complex.conj_ofReal, Complex.real_smul]
  push_cast
  field_simp
end ScalarMeasures
end YangMills.Construction.EuclideanBorel
