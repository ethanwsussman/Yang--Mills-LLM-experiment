import YangMills.Construction.ComplexAnalysis.HalfPiStripIdentityTheoremProof
import YangMills.Construction.Coordinates.PowerSeriesHolomorphy
import YangMills.Construction.EuclideanAnalysis.ExponentialMomentsFromHolomorphyOfTheTransform
import YangMills.Construction.HolomorphicExtension.TubeExtensionFromStripCross
import YangMills.Construction.TwoPoints.ElementaryFactsOfMirrorsAndPlates
import YangMills.Construction.TwoPoints.PropertiesOfThePlaneKernel
import YangMills.Construction.TwoPoints.SpectralMeasuresVanishOutsideTheCone
import Mathlib
set_option autoImplicit false
open MeasureTheory Filter Set
open scoped NNReal ENNReal Topology
noncomputable section
namespace YangMills.Construction.TwoPoints.ConeSupport
open YangMills.Construction.SpectralCalculus
def laplaceIntegrand (s : ℝ) (w : ℂ) (p : SpectralPlane) : ℂ :=
  Complex.exp (-w * ((p.1 : ℝ) : ℂ) + Complex.I * ((s * p.2 : ℝ) : ℂ))
def laplaceFourier (ν : Measure SpectralPlane) (s : ℝ) (w : ℂ) : ℂ :=
  ∫ p, laplaceIntegrand s w p ∂ν
def expMoment (ν : Measure SpectralPlane) (c : ℝ) : ℝ≥0∞ :=
  ∫⁻ p, ENNReal.ofReal (Real.exp (-c * (p.1 : ℝ))) ∂ν
theorem norm_laplaceIntegrand (s : ℝ) (w : ℂ) (p : SpectralPlane) :
    ‖laplaceIntegrand s w p‖ = Real.exp (-w.re * (p.1 : ℝ)) := by
  unfold laplaceIntegrand
  rw [Complex.norm_exp]
  congr 1
  simp
theorem measurable_energyCoord : Measurable fun p : SpectralPlane => (p.1 : ℝ) :=
  measurable_coe_nnreal_real.comp measurable_fst
theorem measurable_laplaceIntegrand (s : ℝ) (w : ℂ) : Measurable (laplaceIntegrand s w) := by
  have h1 : Measurable fun p : SpectralPlane => (((p.1 : ℝ≥0) : ℝ) : ℂ) :=
    Complex.measurable_ofReal.comp measurable_energyCoord
  have h2 : Measurable fun p : SpectralPlane => ((s * p.2 : ℝ) : ℂ) :=
    Complex.measurable_ofReal.comp (measurable_const.mul measurable_snd)
  exact Complex.measurable_exp.comp ((measurable_const.mul h1).add (measurable_const.mul h2))
theorem measurable_expDecay (c : ℝ) :
    Measurable fun p : SpectralPlane => Real.exp (-c * (p.1 : ℝ)) :=
  Real.measurable_exp.comp (measurable_const.mul measurable_energyCoord)
theorem integrable_expDecay {ν : Measure SpectralPlane} {c : ℝ} (h : expMoment ν c < ∞) :
    Integrable (fun p : SpectralPlane => Real.exp (-c * (p.1 : ℝ))) ν :=
  ⟨(measurable_expDecay c).aestronglyMeasurable,
    (hasFiniteIntegral_iff_ofReal (ae_of_all _ fun _ => (Real.exp_pos _).le)).2 h⟩
theorem enorm_laplaceFourier_le (ν : Measure SpectralPlane) (s : ℝ) (w : ℂ) :
    ‖laplaceFourier ν s w‖ₑ ≤ expMoment ν w.re := by
  refine (enorm_integral_le_lintegral_enorm _).trans (lintegral_mono fun p => ?_)
  rw [← ofReal_norm, norm_laplaceIntegrand]
theorem expMoment_antitone (ν : Measure SpectralPlane) {c c' : ℝ} (h : c ≤ c') :
    expMoment ν c' ≤ expMoment ν c := by
  refine lintegral_mono fun p => ENNReal.ofReal_le_ofReal (Real.exp_le_exp.2 ?_)
  have : 0 ≤ (p.1 : ℝ) := p.1.2
  nlinarith
theorem differentiableOn_laplaceFourier {ν : Measure SpectralPlane}
    (hfin : ∀ c : ℝ, 0 < c → expMoment ν c < ∞) (s : ℝ) :
    DifferentiableOn ℂ (laplaceFourier ν s) {w | 0 < w.re} := by
  intro w₀ hw₀
  have hc : 0 < w₀.re := hw₀
  set c := w₀.re with hcdef
  have hint : Integrable (laplaceIntegrand s w₀) ν := by
    refine (integrable_expDecay (hfin c hc)).mono'
      (measurable_laplaceIntegrand s w₀).aestronglyMeasurable (ae_of_all _ fun p => ?_)
    rw [norm_laplaceIntegrand]
  have hbound : Integrable (fun p : SpectralPlane =>
      (4 / c) * Real.exp (-(c / 4) * (p.1 : ℝ))) ν :=
    (integrable_expDecay (hfin (c / 4) (by positivity))).const_mul _
  have hmeas' : Measurable fun p : SpectralPlane =>
      -(((p.1 : ℝ) : ℂ)) * laplaceIntegrand s w₀ p :=
    ((Complex.measurable_ofReal.comp measurable_energyCoord).neg).mul
      (measurable_laplaceIntegrand s w₀)
  have key := hasDerivAt_integral_of_dominated_loc_of_deriv_le (μ := ν) (𝕜 := ℂ)
    (F := fun w p => laplaceIntegrand s w p) (x₀ := w₀)
    (F' := fun w p => -(((p.1 : ℝ) : ℂ)) * laplaceIntegrand s w p)
    (bound := fun p => (4 / c) * Real.exp (-(c / 4) * (p.1 : ℝ)))
    (s := Metric.ball w₀ (c / 2))
    (Metric.ball_mem_nhds _ (by positivity))
    (Eventually.of_forall fun w => (measurable_laplaceIntegrand s w).aestronglyMeasurable)
    hint hmeas'.aestronglyMeasurable
    (ae_of_all _ fun p z hz => ?_) hbound
    (ae_of_all _ fun p z _ => ?_)
  · exact key.2.differentiableAt.differentiableWithinAt
  · have hE : 0 ≤ (p.1 : ℝ) := p.1.2
    have hre : c / 2 ≤ z.re := by
      have h1 : |(z - w₀).re| ≤ ‖z - w₀‖ := Complex.abs_re_le_norm _
      have h2 : ‖z - w₀‖ < c / 2 := by simpa [dist_eq_norm] using hz
      have h3 := abs_le.1 (h1.trans h2.le)
      simp only [Complex.sub_re] at h3
      linarith [h3.1]
    rw [norm_mul, norm_neg, norm_laplaceIntegrand, Complex.norm_real, Real.norm_eq_abs,
      abs_of_nonneg hE]
    have hx : c / 4 * (p.1 : ℝ) ≤ Real.exp (c / 4 * (p.1 : ℝ)) := by
      linarith [Real.add_one_le_exp (c / 4 * (p.1 : ℝ))]
    have hE' : (p.1 : ℝ) ≤ 4 / c * Real.exp (c / 4 * (p.1 : ℝ)) := by
      have : (p.1 : ℝ) = 4 / c * (c / 4 * (p.1 : ℝ)) := by field_simp
      calc (p.1 : ℝ) = 4 / c * (c / 4 * (p.1 : ℝ)) := this
        _ ≤ _ := by gcongr
    have hexp : Real.exp (-z.re * (p.1 : ℝ)) ≤ Real.exp (-(c / 2) * (p.1 : ℝ)) :=
      Real.exp_le_exp.2 (by nlinarith)
    calc (p.1 : ℝ) * Real.exp (-z.re * (p.1 : ℝ))
        ≤ (4 / c * Real.exp (c / 4 * (p.1 : ℝ))) * Real.exp (-(c / 2) * (p.1 : ℝ)) := by
          gcongr
      _ = (4 / c) * Real.exp (-(c / 4) * (p.1 : ℝ)) := by
          rw [mul_assoc, ← Real.exp_add]
          congr 2
          ring
  · have h1 : HasDerivAt (fun w : ℂ => -w * ((p.1 : ℝ) : ℂ) + Complex.I * ((s * p.2 : ℝ) : ℂ))
        (-(((p.1 : ℝ) : ℂ))) z := by
      have := ((hasDerivAt_id z).neg.mul_const (((p.1 : ℝ) : ℂ))).add_const
        (Complex.I * ((s * p.2 : ℝ) : ℂ))
      simpa using this
    have h2 := h1.cexp
    show HasDerivAt (fun w => laplaceIntegrand s w p)
      (-(((p.1 : ℝ) : ℂ)) * laplaceIntegrand s z p) z
    rw [mul_comm]
    exact h2
open YangMills.Construction.Strips
theorem re_exp_pos_of_mem_halfPiStrip {ζ : ℂ} (h : ζ ∈ halfPiStrip) :
    0 < (Complex.exp ζ).re := by
  rw [Complex.exp_re]
  have := abs_lt.1 (show |ζ.im| < Real.pi / 2 from h)
  exact mul_pos (Real.exp_pos _) (Real.cos_pos_of_mem_Ioo ⟨this.1, this.2⟩)
theorem differentiableOn_laplaceFourier_exp {ν : Measure SpectralPlane}
    (hfin : ∀ c : ℝ, 0 < c → expMoment ν c < ∞) (s : ℝ) :
    DifferentiableOn ℂ (fun ζ => laplaceFourier ν s (Complex.exp ζ)) halfPiStrip :=
  (differentiableOn_laplaceFourier hfin s).comp Complex.differentiable_exp.differentiableOn
    fun _ h => re_exp_pos_of_mem_halfPiStrip h
theorem eqOn_halfPiStrip_of_real {f g : ℂ → ℂ} (hf : DifferentiableOn ℂ f halfPiStrip)
    (hg : DifferentiableOn ℂ g halfPiStrip) (h : ∀ t : ℝ, f t = g t) :
    EqOn f g halfPiStrip := by apply _root_.YangMills.Construction.Strips.eqOnHalfPiStripOfEqOnReal <;> assumption
theorem stripExtensionAlong_eq {g : (Fin 2 → ℝ) → ℂ} {j : Fin 2} {x : Fin 2 → ℝ} {F : ℂ → ℂ}
    (hF : IsStripExtensionAlong g j x F) {ζ : ℂ} (hζ : ζ ∈ halfPiStrip) :
    stripExtensionAlong g j x ζ = F ζ := by
  have hE : IsStripExtensionAlong g j x (stripExtensionAlong g j x) :=
    Classical.epsilon_spec (⟨F, hF⟩ : ∃ F, IsStripExtensionAlong g j x F)
  exact eqOn_halfPiStrip_of_real hE.1 hF.1 (fun t => by rw [hE.2 t, hF.2 t]) hζ
section Cross
variable {νp νm : Measure SpectralPlane} {Gt : ℝ → ℝ → ℂ}
def expCoordKernel (Gt : ℝ → ℝ → ℂ) (x : Fin 2 → ℝ) : ℂ :=
  Gt (Real.exp (x 0)) (Real.exp (x 1))
def extensionFirst (νp : Measure SpectralPlane) (x : Fin 2 → ℝ) (ζ : ℂ) : ℂ :=
  laplaceFourier νp (-(Real.exp (x 1))) (Complex.exp ζ)
def extensionSecond (νm : Measure SpectralPlane) (x : Fin 2 → ℝ) (ζ : ℂ) : ℂ :=
  laplaceFourier νm (Real.exp (x 0)) (Complex.exp ζ)
theorem isStripExtensionAlong_zero (hfp : ∀ c : ℝ, 0 < c → expMoment νp c < ∞)
    (hp : ∀ a b : ℝ, 0 < a → Gt a b = laplaceFourier νp (-b) a) (x : Fin 2 → ℝ) :
    IsStripExtensionAlong (expCoordKernel Gt) 0 x (extensionFirst νp x) := by
  refine ⟨differentiableOn_laplaceFourier_exp hfp _, fun t => ?_⟩
  have h1 : Function.update x 0 t 1 = x 1 := Function.update_of_ne (by decide) _ _
  simp only [extensionFirst, expCoordKernel, Function.update_self]
  rw [h1, hp _ _ (Real.exp_pos t), Complex.ofReal_exp]
theorem isStripExtensionAlong_one (hfm : ∀ c : ℝ, 0 < c → expMoment νm c < ∞)
    (hm : ∀ a b : ℝ, 0 < b → Gt a b = laplaceFourier νm a b) (x : Fin 2 → ℝ) :
    IsStripExtensionAlong (expCoordKernel Gt) 1 x (extensionSecond νm x) := by
  refine ⟨differentiableOn_laplaceFourier_exp hfm _, fun t => ?_⟩
  have h1 : Function.update x 1 t 0 = x 0 := Function.update_of_ne (by decide) _ _
  simp only [extensionSecond, expCoordKernel, Function.update_self]
  rw [h1, hm _ _ (Real.exp_pos t), Complex.ofReal_exp]
theorem exp_mul_cos_le_re_exp {ζ : ℂ} {x y T b : ℝ} (hb : 0 ≤ b) (hb' : b < Real.pi / 2)
    (h1 : |ζ.re - x| ≤ T) (h2 : |ζ.im| ≤ b) (hy : y ≤ x) :
    Real.exp (y - T) * Real.cos b ≤ (Complex.exp ζ).re := by
  rw [Complex.exp_re]
  have hc : Real.cos b ≤ Real.cos ζ.im := by
    rw [← Real.cos_abs ζ.im]
    exact Real.cos_le_cos_of_nonneg_of_le_pi (abs_nonneg _) (by linarith [Real.pi_pos]) h2
  have hc0 : 0 ≤ Real.cos b :=
    (Real.cos_pos_of_mem_Ioo ⟨by linarith [Real.pi_pos], hb'⟩).le
  have he : Real.exp (y - T) ≤ Real.exp ζ.re :=
    Real.exp_le_exp.2 (by linarith [(abs_le.1 h1).1])
  exact mul_le_mul he hc hc0 (Real.exp_pos _).le
theorem fin_two_eq_zero_or_one (j : Fin 2) : j = 0 ∨ j = 1 := by
  fin_cases j <;> simp
theorem supOnCross_le (hfp : ∀ c : ℝ, 0 < c → expMoment νp c < ∞)
    (hfm : ∀ c : ℝ, 0 < c → expMoment νm c < ∞)
    (hp : ∀ a b : ℝ, 0 < a → Gt a b = laplaceFourier νp (-b) a)
    (hm : ∀ a b : ℝ, 0 < b → Gt a b = laplaceFourier νm a b)
    (x : Fin 2 → ℝ) (T b : ℝ) (hb : 0 ≤ b) (hb' : b < Real.pi / 2) :
    supOnCross (expCoordKernel Gt) x T b ≤
      expMoment νp (Real.exp (min (x 0) (x 1) - T) * Real.cos b) +
        expMoment νm (Real.exp (min (x 0) (x 1) - T) * Real.cos b) := by
  refine sSup_le ?_
  rintro r ⟨j, z, hz, rfl⟩
  obtain ⟨h1, h2, -⟩ := hz
  have hstrip : z j ∈ halfPiStrip := lt_of_le_of_lt h2 hb'
  rcases fin_two_eq_zero_or_one j with rfl | rfl
  · have e : valueAlong (expCoordKernel Gt) 0 z =
        extensionFirst νp (fun i => (z i).re) (z 0) :=
      stripExtensionAlong_eq (isStripExtensionAlong_zero hfp hp _) hstrip
    rw [e]
    refine le_trans ?_ le_self_add
    exact (enorm_laplaceFourier_le _ _ _).trans
      (expMoment_antitone _ (exp_mul_cos_le_re_exp hb hb' h1 h2 (min_le_left _ _)))
  · have e : valueAlong (expCoordKernel Gt) 1 z =
        extensionSecond νm (fun i => (z i).re) (z 1) :=
      stripExtensionAlong_eq (isStripExtensionAlong_one hfm hm _) hstrip
    rw [e]
    refine le_trans ?_ le_add_self
    exact (enorm_laplaceFourier_le _ _ _).trans
      (expMoment_antitone _ (exp_mul_cos_le_re_exp hb hb' h1 h2 (min_le_right _ _)))
theorem isSepHolomorphicOnStrips_expCoordKernel (hfp : ∀ c : ℝ, 0 < c → expMoment νp c < ∞)
    (hfm : ∀ c : ℝ, 0 < c → expMoment νm c < ∞)
    (hp : ∀ a b : ℝ, 0 < a → Gt a b = laplaceFourier νp (-b) a)
    (hm : ∀ a b : ℝ, 0 < b → Gt a b = laplaceFourier νm a b)
    (hcont : ContinuousOn (fun p : ℝ × ℝ => Gt p.1 p.2) {p | 0 < p.1 ∧ 0 < p.2}) :
    IsSepHolomorphicOnStrips (expCoordKernel Gt) := by
  refine ⟨?_, fun j x => ?_⟩
  · have h : Continuous fun x : Fin 2 → ℝ => (Real.exp (x 0), Real.exp (x 1)) := by fun_prop
    exact hcont.comp_continuous h fun x => ⟨Real.exp_pos _, Real.exp_pos _⟩
  · rcases fin_two_eq_zero_or_one j with rfl | rfl
    · exact ⟨_, isStripExtensionAlong_zero hfp hp x⟩
    · exact ⟨_, isStripExtensionAlong_one hfm hm x⟩
end Cross
theorem tubeExtension_two (hHull : HolomorphicExtension.TubeExtensionFromStripCross)
    {g : (Fin 2 → ℝ) → ℂ} (hg : IsSepHolomorphicOnStrips g)
    (hA : ∀ (x : Fin 2 → ℝ) (T b : ℝ), 0 ≤ T → 0 ≤ b → b < Real.pi / 2 →
      supOnCross g x T b < ∞) :
    ∃ gHat : Coordinates.ComplexCoordinates 2 → ℂ,
      Coordinates.ComplexCoordinates.IsHolomorphicIn (N' := 1) (halfPiTube 2)
        (fun z _ => gHat z) ∧
      (∀ x : Fin 2 → ℝ, gHat (fun j => (x j : ℂ)) = g x) ∧
      ∀ ε : ℝ, 0 < ε → ε ≤ 1 →
        HolomorphicExtension.HullConstants.halfWidth ε < Real.pi / 2 ∧
        ∀ x v : Fin 2 → ℝ, ∑ j, |v j| ≤ (1 - ε) * (Real.pi / 2) →
          ‖gHat (fun j => (x j : ℂ) + (v j : ℂ) * Complex.I)‖ₑ ≤
            ENNReal.ofReal (HolomorphicExtension.HullConstants.boundFactor 2 ε) *
              supOnCross g x (HolomorphicExtension.HullConstants.radius ε)
                (HolomorphicExtension.HullConstants.halfWidth ε) :=
  hHull 2 g hg hA
theorem abs_arctan_eq (y : ℝ) : |Real.arctan y| = Real.arctan |y| := by
  rcases le_total 0 y with h | h
  · have h0 : 0 ≤ Real.arctan y := by simpa using Real.arctan_strictMono.monotone h
    rw [abs_of_nonneg h, abs_of_nonneg h0]
  · have h0 : Real.arctan y ≤ 0 := by simpa using Real.arctan_strictMono.monotone h
    rw [abs_of_nonpos h, abs_of_nonpos h0, Real.arctan_neg]
theorem abs_im_log_of_re_pos {w : ℂ} (hw : 0 < w.re) :
    |(Complex.log w).im| = Real.arctan (|w.im| / w.re) := by
  have h : (Complex.log w).im = Real.arctan (w.im / w.re) := by
    rw [← rightHalfPlaneLog_eq_log hw, rightHalfPlaneLog, Complex.add_im, Complex.ofReal_im,
      Complex.mul_im, Complex.I_re, Complex.I_im, Complex.ofReal_im, Complex.ofReal_re]
    ring
  rw [h, abs_arctan_eq, abs_div, abs_of_pos hw]
def diagLogPoint (t : ℝ) (s : ℂ) : Coordinates.ComplexCoordinates 2 :=
  ![Complex.log (((t : ℂ) + s) / (Real.sqrt 2 : ℂ)),
    Complex.log (((t : ℂ) - s) / (Real.sqrt 2 : ℂ))]
theorem sqrtTwo_pos : 0 < Real.sqrt 2 := by positivity
theorem re_add_div_sqrt_two {t : ℝ} {s : ℂ} : (((t : ℂ) + s) / (Real.sqrt 2 : ℂ)).re =
    (t + s.re) / Real.sqrt 2 := by
  rw [Complex.div_ofReal_re]
  simp
theorem re_sub_div_sqrt_two {t : ℝ} {s : ℂ} : (((t : ℂ) - s) / (Real.sqrt 2 : ℂ)).re =
    (t - s.re) / Real.sqrt 2 := by
  rw [Complex.div_ofReal_re]
  simp
theorem im_add_div_sqrt_two {t : ℝ} {s : ℂ} : (((t : ℂ) + s) / (Real.sqrt 2 : ℂ)).im =
    s.im / Real.sqrt 2 := by
  rw [Complex.div_ofReal_im]
  simp
theorem im_sub_div_sqrt_two {t : ℝ} {s : ℂ} : (((t : ℂ) - s) / (Real.sqrt 2 : ℂ)).im =
    -s.im / Real.sqrt 2 := by
  rw [Complex.div_ofReal_im]
  simp
theorem re_add_div_sqrt_two_pos {t : ℝ} {s : ℂ} (hs : ‖s‖ < t) :
    0 < (((t : ℂ) + s) / (Real.sqrt 2 : ℂ)).re := by
  have h := abs_lt.1 ((Complex.abs_re_le_norm s).trans_lt hs)
  rw [re_add_div_sqrt_two]
  exact div_pos (by linarith [h.1]) sqrtTwo_pos
theorem re_sub_div_sqrt_two_pos {t : ℝ} {s : ℂ} (hs : ‖s‖ < t) :
    0 < (((t : ℂ) - s) / (Real.sqrt 2 : ℂ)).re := by
  have h := abs_lt.1 ((Complex.abs_re_le_norm s).trans_lt hs)
  rw [re_sub_div_sqrt_two]
  exact div_pos (by linarith [h.2]) sqrtTwo_pos
theorem diagLogPoint_mem_halfPiTube {t : ℝ} {s : ℂ} (hs : ‖s‖ < t) :
    diagLogPoint t s ∈ halfPiTube 2 := by
  have hre := abs_lt.1 ((Complex.abs_re_le_norm s).trans_lt hs)
  have ha : 0 < t + s.re := by linarith [hre.1]
  have hb : 0 < t - s.re := by linarith [hre.2]
  have hr := sqrtTwo_pos
  have e1 : |(((t : ℂ) + s) / (Real.sqrt 2 : ℂ)).im| / (((t : ℂ) + s) / (Real.sqrt 2 : ℂ)).re =
      |s.im| / (t + s.re) := by
    rw [im_add_div_sqrt_two, re_add_div_sqrt_two, abs_div, abs_of_pos hr]
    field_simp
  have e2 : |(((t : ℂ) - s) / (Real.sqrt 2 : ℂ)).im| / (((t : ℂ) - s) / (Real.sqrt 2 : ℂ)).re =
      |s.im| / (t - s.re) := by
    rw [im_sub_div_sqrt_two, re_sub_div_sqrt_two, abs_div, abs_of_pos hr, abs_neg]
    field_simp
  have hxy : |s.im| / (t + s.re) * (|s.im| / (t - s.re)) < 1 := by
    rw [div_mul_div_comm, div_lt_one (by positivity), abs_mul_abs_self]
    have h1 : s.re * s.re + s.im * s.im = ‖s‖ ^ 2 := by
      rw [Complex.sq_norm, Complex.normSq_apply]
    have h2 : ‖s‖ ^ 2 < t ^ 2 := by
      have := norm_nonneg s
      nlinarith
    nlinarith
  show ∑ j : Fin 2, |(diagLogPoint t s j).im| < Real.pi / 2
  rw [Fin.sum_univ_two]
  show |(Complex.log (((t : ℂ) + s) / (Real.sqrt 2 : ℂ))).im| +
    |(Complex.log (((t : ℂ) - s) / (Real.sqrt 2 : ℂ))).im| < Real.pi / 2
  rw [abs_im_log_of_re_pos (re_add_div_sqrt_two_pos hs),
    abs_im_log_of_re_pos (re_sub_div_sqrt_two_pos hs), e1, e2, Real.arctan_add hxy]
  exact Real.arctan_lt_pi_div_two _
theorem differentiableAt_diagLogPoint {t : ℝ} {s : ℂ} (hs : ‖s‖ < t) :
    DifferentiableAt ℂ (diagLogPoint t) s := by
  rw [differentiableAt_pi]
  intro j
  rcases fin_two_eq_zero_or_one j with rfl | rfl
  · show DifferentiableAt ℂ (fun s : ℂ => Complex.log (((t : ℂ) + s) / (Real.sqrt 2 : ℂ))) s
    exact DifferentiableAt.clog (by fun_prop)
      (Complex.mem_slitPlane_iff.2 (Or.inl (re_add_div_sqrt_two_pos hs)))
  · show DifferentiableAt ℂ (fun s : ℂ => Complex.log (((t : ℂ) - s) / (Real.sqrt 2 : ℂ))) s
    exact DifferentiableAt.clog (by fun_prop)
      (Complex.mem_slitPlane_iff.2 (Or.inl (re_sub_div_sqrt_two_pos hs)))
def discRestriction (gHat : Coordinates.ComplexCoordinates 2 → ℂ) (t : ℝ) (s : ℂ) : ℂ :=
  gHat (diagLogPoint t s)
theorem differentiableOn_discRestriction
    (hMx : Coordinates.ComplexCoordinates.PowerSeriesHolomorphy.Properties)
    {gHat : Coordinates.ComplexCoordinates 2 → ℂ}
    (hg : Coordinates.ComplexCoordinates.IsHolomorphicIn (N' := 1) (halfPiTube 2)
      (fun z _ => gHat z)) (t : ℝ) :
    DifferentiableOn ℂ (discRestriction gHat t) (Metric.ball 0 t) := by
  intro s hs
  have hs' : ‖s‖ < t := by simpa using hs
  obtain ⟨L, hL⟩ := ((hMx.1 2 _ hg.1).1 1 _ hg).2.2.1 (diagLogPoint t s)
    (diagLogPoint_mem_halfPiTube hs')
  have hL' : HasFDerivAt (𝕜 := ℂ)
      (fun z : Coordinates.ComplexCoordinates 2 => (fun _ : Fin 1 => gHat z)) L
      (diagLogPoint t s) := hasFDerivAt_of_restrictScalars ℝ hL rfl
  have hc : DifferentiableAt ℂ (fun z : Coordinates.ComplexCoordinates 2 => gHat z)
      (diagLogPoint t s) :=
    differentiableAt_pi.1 hL'.differentiableAt 0
  exact (hc.comp s (differentiableAt_diagLogPoint hs')).differentiableWithinAt
theorem discRestriction_ofReal {Gt : ℝ → ℝ → ℂ} {gHat : Coordinates.ComplexCoordinates 2 → ℂ}
    (hres : ∀ x : Fin 2 → ℝ, gHat (fun j => (x j : ℂ)) = expCoordKernel Gt x) {t s : ℝ}
    (hs : |s| < t) :
    discRestriction gHat t s = Gt ((t + s) / Real.sqrt 2) ((t - s) / Real.sqrt 2) := by
  have h := abs_lt.1 hs
  have hp : 0 < (t + s) / Real.sqrt 2 := div_pos (by linarith [h.1]) sqrtTwo_pos
  have hm : 0 < (t - s) / Real.sqrt 2 := div_pos (by linarith [h.2]) sqrtTwo_pos
  have e : diagLogPoint t s = fun j => (((![Real.log ((t + s) / Real.sqrt 2),
      Real.log ((t - s) / Real.sqrt 2)] : Fin 2 → ℝ) j : ℝ) : ℂ) := by
    funext j
    rcases fin_two_eq_zero_or_one j with rfl | rfl
    · show Complex.log (((t : ℂ) + s) / (Real.sqrt 2 : ℂ)) =
        ((Real.log ((t + s) / Real.sqrt 2) : ℝ) : ℂ)
      rw [Complex.ofReal_log hp.le]
      push_cast
      rfl
    · show Complex.log (((t : ℂ) - s) / (Real.sqrt 2 : ℂ)) =
        ((Real.log ((t - s) / Real.sqrt 2) : ℝ) : ℂ)
      rw [Complex.ofReal_log hm.le]
      push_cast
      rfl
  rw [discRestriction, e, hres]
  simp [expCoordKernel, Real.exp_log hp, Real.exp_log hm]
theorem discRestriction_bounded {νp νm : Measure SpectralPlane} {Gt : ℝ → ℝ → ℂ}
    (hfp : ∀ c : ℝ, 0 < c → expMoment νp c < ∞)
    (hfm : ∀ c : ℝ, 0 < c → expMoment νm c < ∞)
    (hp : ∀ a b : ℝ, 0 < a → Gt a b = laplaceFourier νp (-b) a)
    (hm : ∀ a b : ℝ, 0 < b → Gt a b = laplaceFourier νm a b)
    {gHat : Coordinates.ComplexCoordinates 2 → ℂ}
    (hb : ∀ ε : ℝ, 0 < ε → ε ≤ 1 →
        HolomorphicExtension.HullConstants.halfWidth ε < Real.pi / 2 ∧
        ∀ x v : Fin 2 → ℝ, ∑ j, |v j| ≤ (1 - ε) * (Real.pi / 2) →
          ‖gHat (fun j => (x j : ℂ) + (v j : ℂ) * Complex.I)‖ₑ ≤
            ENNReal.ofReal (HolomorphicExtension.HullConstants.boundFactor 2 ε) *
              supOnCross (expCoordKernel Gt) x (HolomorphicExtension.HullConstants.radius ε)
                (HolomorphicExtension.HullConstants.halfWidth ε))
    {ε : ℝ} (hε : 0 < ε) (hε' : ε < 1) :
    ∃ K : ℝ≥0∞, K < ∞ ∧ ∀ t η : ℝ, 1 ≤ t → |η| ≤ (1 - ε) * t →
      ‖discRestriction gHat t (Complex.I * (η : ℂ))‖ₑ ≤ K := by
  have hpi := Real.pi_pos
  have harc0 : 0 < Real.arctan (1 - ε) := by
    have := Real.arctan_strictMono (show (0 : ℝ) < 1 - ε by linarith)
    simpa using this
  have harc1 : Real.arctan (1 - ε) < Real.pi / 4 := by
    have := Real.arctan_strictMono (show 1 - ε < (1 : ℝ) by linarith)
    simpa [Real.arctan_one] using this
  set κ : ℝ := 4 / Real.pi * Real.arctan (1 - ε) with hκ
  have hκ0 : 0 < κ := by positivity
  have hκ1 : κ < 1 := by
    rw [hκ, div_mul_eq_mul_div, div_lt_one hpi]
    linarith
  have hκπ : (1 - (1 - κ)) * (Real.pi / 2) = 2 * Real.arctan (1 - ε) := by
    rw [hκ]
    field_simp
    ring
  obtain ⟨hb', hbound⟩ := hb (1 - κ) (by linarith) (by linarith)
  set T := HolomorphicExtension.HullConstants.radius (1 - κ)
  set b := HolomorphicExtension.HullConstants.halfWidth (1 - κ) with hbdef
  have hb0 : 0 ≤ b := by
    have : b = (1 - (1 - κ) / 2) * (Real.pi / 2) := rfl
    rw [this]
    have : 0 ≤ 1 - (1 - κ) / 2 := by linarith
    positivity
  have hcos : 0 < Real.cos b := Real.cos_pos_of_mem_Ioo ⟨by linarith, hb'⟩
  have hr := sqrtTwo_pos
  set c₀ : ℝ := Real.exp (-T) * Real.cos b / Real.sqrt 2 with hc₀
  have hc₀pos : 0 < c₀ := by positivity
  refine ⟨ENNReal.ofReal (HolomorphicExtension.HullConstants.boundFactor 2 (1 - κ)) *
    (expMoment νp c₀ + expMoment νm c₀),
    ENNReal.mul_lt_top ENNReal.ofReal_lt_top
      (ENNReal.add_lt_top.2 ⟨hfp _ hc₀pos, hfm _ hc₀pos⟩), fun t η ht hη => ?_⟩
  have htpos : 0 < t := by linarith
  set u : ℂ := ((t : ℂ) + Complex.I * (η : ℂ)) / (Real.sqrt 2 : ℂ) with hu
  have hηt : ‖Complex.I * (η : ℂ)‖ < t := by
    have : ‖Complex.I * (η : ℂ)‖ = |η| := by simp
    rw [this]
    nlinarith
  have hure : 0 < u.re := re_add_div_sqrt_two_pos hηt
  have hure' : u.re = t / Real.sqrt 2 := by
    rw [hu, re_add_div_sqrt_two]
    simp
  have huim : u.im = η / Real.sqrt 2 := by
    rw [hu, im_add_div_sqrt_two]
    simp
  set a : ℝ := Real.log ‖u‖ with ha
  set θ : ℝ := (Complex.log u).im with hθ
  have hconj : ((t : ℂ) - Complex.I * (η : ℂ)) / (Real.sqrt 2 : ℂ) = (starRingEnd ℂ) u := by
    rw [hu, map_div₀, map_add, map_mul, Complex.conj_I, Complex.conj_ofReal,
      Complex.conj_ofReal, Complex.conj_ofReal]
    ring
  have harg : u.arg ≠ Real.pi := by
    intro h
    have := (Complex.arg_eq_pi_iff.1 h).1
    linarith
  have hlog : Complex.log u = (a : ℂ) + (θ : ℂ) * Complex.I := by
    apply Complex.ext
    · simp [hθ, ha, Complex.log_re]
    · simp [hθ]
  have e : diagLogPoint t (Complex.I * (η : ℂ)) =
      fun j => (((fun _ => a) j : ℝ) : ℂ) + (((![θ, -θ] : Fin 2 → ℝ) j : ℝ) : ℂ) * Complex.I := by
    funext j
    rcases fin_two_eq_zero_or_one j with rfl | rfl
    · show Complex.log u = (a : ℂ) + (θ : ℂ) * Complex.I
      exact hlog
    · show Complex.log (((t : ℂ) - Complex.I * (η : ℂ)) / (Real.sqrt 2 : ℂ)) =
        (a : ℂ) + ((-θ : ℝ) : ℂ) * Complex.I
      rw [hconj, Complex.log_conj _ harg, hlog]
      simp [Complex.conj_ofReal]
  have hsum : ∑ j, |(![θ, -θ] : Fin 2 → ℝ) j| ≤ (1 - (1 - κ)) * (Real.pi / 2) := by
    rw [Fin.sum_univ_two, hκπ]
    show |θ| + |-θ| ≤ _
    rw [abs_neg, hθ, abs_im_log_of_re_pos hure, hure', huim, abs_div, abs_of_pos hr]
    have h1 : |η| / Real.sqrt 2 / (t / Real.sqrt 2) ≤ 1 - ε := by
      have : |η| / Real.sqrt 2 / (t / Real.sqrt 2) = |η| / t := by field_simp
      rw [this, div_le_iff₀ htpos]
      exact hη
    have := Real.arctan_strictMono.monotone h1
    linarith
  have hmain := hbound (fun _ => a) ![θ, -θ] hsum
  rw [discRestriction, e]
  refine hmain.trans (mul_le_mul_right ?_ _)
  refine (supOnCross_le hfp hfm hp hm _ _ _ hb0 hb').trans ?_
  have hc : c₀ ≤ Real.exp (min a a - T) * Real.cos b := by
    have hnorm : t / Real.sqrt 2 ≤ Real.exp a := by
      rw [ha, Real.exp_log (lt_of_lt_of_le hure (Complex.re_le_norm u)), ← hure']
      exact Complex.re_le_norm u
    have h1 : 1 / Real.sqrt 2 ≤ Real.exp a :=
      le_trans (div_le_div_of_nonneg_right ht hr.le) hnorm
    rw [min_self, sub_eq_add_neg, Real.exp_add, hc₀]
    have h2 : 0 < Real.exp (-T) * Real.cos b := by positivity
    calc Real.exp (-T) * Real.cos b / Real.sqrt 2
        = 1 / Real.sqrt 2 * (Real.exp (-T) * Real.cos b) := by ring
      _ ≤ Real.exp a * (Real.exp (-T) * Real.cos b) := by gcongr
      _ = _ := by ring
  exact add_le_add (expMoment_antitone _ hc) (expMoment_antitone _ hc)
theorem cosh_le_exp_abs_self (x : ℝ) : Real.cosh x ≤ Real.exp |x| := by
  rw [← Real.cosh_abs, Real.cosh_eq]
  have : Real.exp (-|x|) ≤ Real.exp |x| := Real.exp_le_exp.2 (by linarith [abs_nonneg x])
  linarith
theorem exp_abs_div_two_le_cosh (x : ℝ) : Real.exp |x| / 2 ≤ Real.cosh x := by
  rw [← Real.cosh_abs, Real.cosh_eq]
  have := Real.exp_pos (-|x|)
  linarith
theorem weighted_mass_le
    (hM : EuclideanAnalysis.HolomorphicCharFun.ExpMomentsOfHolomorphicCharFun)
    {ν : Measure SpectralPlane} {Gt : ℝ → ℝ → ℂ}
    (hfin : ∀ c : ℝ, 0 < c → expMoment ν c < ∞)
    (h0 : ∀ t s : ℝ, 0 < t →
      Gt ((t + s) / Real.sqrt 2) ((t - s) / Real.sqrt 2) = laplaceFourier ν s t)
    {gHat : Coordinates.ComplexCoordinates 2 → ℂ}
    (hd : ∀ t : ℝ, DifferentiableOn ℂ (discRestriction gHat t) (Metric.ball 0 t))
    (hr : ∀ t s : ℝ, |s| < t →
      discRestriction gHat t s = Gt ((t + s) / Real.sqrt 2) ((t - s) / Real.sqrt 2))
    {ε ε₁ : ℝ} (hε : 0 < ε) (hε' : ε < 1) {K : ℝ≥0∞}
    (hK : ∀ t η : ℝ, 1 ≤ t → |η| ≤ (1 - ε) * t →
      ‖discRestriction gHat t (Complex.I * (η : ℂ))‖ₑ ≤ K)
    {t : ℝ} (ht : 1 ≤ t) :
    ENNReal.ofReal (Real.exp (ε₁ * t) / 2) *
      ν {p : SpectralPlane | ε₁ ≤ (1 - ε) * |p.2| - (p.1 : ℝ)} ≤ K + K := by
  have htpos : 0 < t := by linarith
  set dens : SpectralPlane → ℝ≥0∞ := fun p => ENNReal.ofReal (Real.exp (-t * (p.1 : ℝ)))
    with hdensdef
  have hdens : Measurable dens := ENNReal.measurable_ofReal.comp (measurable_expDecay t)
  have : IsFiniteMeasure (ν.withDensity dens) := isFiniteMeasure_withDensity (hfin t htpos).ne
  set 𝔪 : Measure ℝ := (ν.withDensity dens).map Prod.snd with h𝔪
  have htr : ∀ s ∈ Ioo (-t) t,
      EuclideanAnalysis.measureCharFun 𝔪 s = discRestriction gHat t s := by
    intro s hs
    rw [hr t s (abs_lt.2 hs), h0 t s htpos]
    show ∫ q, Complex.exp (Complex.I * s * q) ∂𝔪 = ∫ p, laplaceIntegrand s t p ∂ν
    have hm : Measurable fun q : ℝ => Complex.exp (Complex.I * s * q) := by fun_prop
    rw [h𝔪, integral_map measurable_snd.aemeasurable hm.aestronglyMeasurable,
      integral_withDensity_eq_integral_toReal_smul hdens
        (Eventually.of_forall fun _ => ENNReal.ofReal_lt_top)]
    congr 1
    funext p
    rw [hdensdef]
    simp only
    rw [ENNReal.toReal_ofReal (Real.exp_pos _).le, Complex.real_smul, laplaceIntegrand,
      Complex.ofReal_exp, ← Complex.exp_add]
    congr 1
    push_cast
    ring
  set η : ℝ := (1 - ε) * t with hη
  have hη0 : 0 ≤ η := by
    have : 0 ≤ 1 - ε := by linarith
    positivity
  have hηt : η < t := by
    rw [hη]
    nlinarith
  obtain ⟨hfinite, hcosh⟩ := hM 𝔪 t (discRestriction gHat t) htpos (hd t) htr η hη0 hηt
  have hmc : Measurable fun q : ℝ => Real.cosh (η * q) :=
    Real.continuous_cosh.measurable.comp (measurable_const.mul measurable_id)
  have hme : Measurable fun q : ℝ => Real.exp (η * |q|) :=
    Real.measurable_exp.comp (measurable_const.mul measurable_id.abs)
  have hinte : Integrable (fun q : ℝ => Real.exp (η * |q|)) 𝔪 :=
    ⟨hme.aestronglyMeasurable,
      (hasFiniteIntegral_iff_ofReal (ae_of_all _ fun _ => (Real.exp_pos _).le)).2 hfinite⟩
  have hint : Integrable (fun q : ℝ => Real.cosh (η * q)) 𝔪 := by
    refine hinte.mono' hmc.aestronglyMeasurable (ae_of_all _ fun q => ?_)
    rw [Real.norm_eq_abs, abs_of_pos (Real.cosh_pos _)]
    refine (cosh_le_exp_abs_self _).trans (le_of_eq ?_)
    rw [abs_mul, abs_of_nonneg hη0]
  have e1 : ENNReal.ofReal (∫ q, Real.cosh (η * q) ∂𝔪) ≤ K + K := by
    have h1 : ENNReal.ofReal (∫ q, Real.cosh (η * q) ∂𝔪) ≤
        ‖((∫ q, Real.cosh (η * q) ∂𝔪 : ℝ) : ℂ)‖ₑ := by
      rw [← ofReal_norm, Complex.norm_real, Real.norm_eq_abs]
      exact ENNReal.ofReal_le_ofReal (le_abs_self _)
    refine h1.trans ?_
    rw [hcosh, enorm_mul]
    have hhalf : ‖(1 / 2 : ℂ)‖ₑ ≤ 1 := by
      rw [← ofReal_norm]
      simp only [one_div, norm_inv, Complex.norm_ofNat]
      exact ENNReal.ofReal_le_one.2 (by norm_num)
    have hneg : Complex.I * ((-η : ℝ) : ℂ) = -(Complex.I * (η : ℂ)) := by
      push_cast
      ring
    have ha := hK t η ht (by rw [abs_of_nonneg hη0])
    have hb := hK t (-η) ht (by rw [abs_neg, abs_of_nonneg hη0])
    rw [hneg] at hb
    calc ‖(1 / 2 : ℂ)‖ₑ * ‖discRestriction gHat t (Complex.I * (η : ℂ)) +
          discRestriction gHat t (-(Complex.I * (η : ℂ)))‖ₑ
        ≤ 1 * (‖discRestriction gHat t (Complex.I * (η : ℂ))‖ₑ +
          ‖discRestriction gHat t (-(Complex.I * (η : ℂ)))‖ₑ) :=
          mul_le_mul' hhalf (enorm_add_le _ _)
      _ ≤ K + K := by
          rw [one_mul]
          exact add_le_add ha hb
  have e2 : ENNReal.ofReal (∫ q, Real.cosh (η * q) ∂𝔪) =
      ∫⁻ q, ENNReal.ofReal (Real.cosh (η * q)) ∂𝔪 :=
    ofReal_integral_eq_lintegral_ofReal hint (ae_of_all _ fun _ => (Real.cosh_pos _).le)
  have hmo : Measurable fun q : ℝ => ENNReal.ofReal (Real.cosh (η * q)) :=
    ENNReal.measurable_ofReal.comp hmc
  have e3 : ∫⁻ q, ENNReal.ofReal (Real.cosh (η * q)) ∂𝔪 =
      ∫⁻ p, dens p * ENNReal.ofReal (Real.cosh (η * p.2)) ∂ν := by
    rw [h𝔪, lintegral_map hmo measurable_snd]
    exact lintegral_withDensity_eq_lintegral_mul ν hdens (hmo.comp measurable_snd)
  have hA : MeasurableSet {p : SpectralPlane | ε₁ ≤ (1 - ε) * |p.2| - (p.1 : ℝ)} :=
    measurableSet_le measurable_const
      ((measurable_const.mul measurable_snd.abs).sub measurable_energyCoord)
  have e4 : ENNReal.ofReal (Real.exp (ε₁ * t) / 2) *
      ν {p : SpectralPlane | ε₁ ≤ (1 - ε) * |p.2| - (p.1 : ℝ)} ≤
      ∫⁻ p, dens p * ENNReal.ofReal (Real.cosh (η * p.2)) ∂ν := by
    rw [← lintegral_indicator_const hA]
    refine lintegral_mono fun p => ?_
    by_cases hpA : p ∈ {p : SpectralPlane | ε₁ ≤ (1 - ε) * |p.2| - (p.1 : ℝ)}
    · rw [indicator_of_mem hpA, hdensdef]
      simp only
      rw [← ENNReal.ofReal_mul (Real.exp_pos _).le]
      refine ENNReal.ofReal_le_ofReal ?_
      have hp : ε₁ ≤ (1 - ε) * |p.2| - (p.1 : ℝ) := hpA
      have h1 := exp_abs_div_two_le_cosh (η * p.2)
      rw [abs_mul, abs_of_nonneg hη0] at h1
      have h2 : Real.exp (ε₁ * t) ≤ Real.exp (-t * (p.1 : ℝ)) * Real.exp (η * |p.2|) := by
        rw [← Real.exp_add]
        refine Real.exp_le_exp.2 ?_
        have : t * ε₁ ≤ t * ((1 - ε) * |p.2| - (p.1 : ℝ)) := by gcongr
        rw [hη]
        linarith
      calc Real.exp (ε₁ * t) / 2
          ≤ Real.exp (-t * (p.1 : ℝ)) * Real.exp (η * |p.2|) / 2 := by gcongr
        _ = Real.exp (-t * (p.1 : ℝ)) * (Real.exp (η * |p.2|) / 2) := by ring
        _ ≤ _ := by gcongr
    · rw [indicator_of_notMem hpA]
      exact zero_le
  calc _ ≤ ∫⁻ p, dens p * ENNReal.ofReal (Real.cosh (η * p.2)) ∂ν := e4
    _ = ENNReal.ofReal (∫ q, Real.cosh (η * q) ∂𝔪) := by rw [e2, e3]
    _ ≤ K + K := e1
theorem measure_eq_zero_of_exp_weighted_le {ν : Measure SpectralPlane} {A : Set SpectralPlane}
    {ε₁ : ℝ} (hε₁ : 0 < ε₁) {K : ℝ≥0∞} (hK : K < ∞)
    (h : ∀ t : ℝ, 1 ≤ t → ENNReal.ofReal (Real.exp (ε₁ * t) / 2) * ν A ≤ K) : ν A = 0 := by
  by_contra hne
  obtain ⟨r, hr0, hrA⟩ := ENNReal.lt_iff_exists_nnreal_btwn.1 (pos_iff_ne_zero.2 hne)
  have hr : 0 < (r : ℝ) := by exact_mod_cast hr0
  set M := K.toReal with hM
  set t : ℝ := max 1 (2 * (M + 1) / r / ε₁) with htdef
  have ht : 1 ≤ t := le_max_left _ _
  have h1 : 2 * (M + 1) / r ≤ ε₁ * t := by
    have : 2 * (M + 1) / r / ε₁ ≤ t := le_max_right _ _
    rw [div_le_iff₀ hε₁] at this
    linarith
  have h2 : 2 * (M + 1) / r ≤ Real.exp (ε₁ * t) :=
    h1.trans (by linarith [Real.add_one_le_exp (ε₁ * t)])
  have h3 : M + 1 ≤ Real.exp (ε₁ * t) / 2 * r := by
    rw [div_le_iff₀ hr] at h2
    linarith
  have h4 : ENNReal.ofReal (M + 1) ≤ K := by
    calc ENNReal.ofReal (M + 1) ≤ ENNReal.ofReal (Real.exp (ε₁ * t) / 2 * r) :=
          ENNReal.ofReal_le_ofReal h3
      _ = ENNReal.ofReal (Real.exp (ε₁ * t) / 2) * r := by
          rw [ENNReal.ofReal_mul (by positivity), ENNReal.ofReal_coe_nnreal]
      _ ≤ ENNReal.ofReal (Real.exp (ε₁ * t) / 2) * ν A := by gcongr
      _ ≤ K := h t ht
  have h5 : M + 1 ≤ M := (ENNReal.ofReal_le_iff_le_toReal hK.ne).1 h4
  linarith
theorem measure_outside_cone_eq_zero (hHull : HolomorphicExtension.TubeExtensionFromStripCross)
    (hM : EuclideanAnalysis.HolomorphicCharFun.ExpMomentsOfHolomorphicCharFun)
    (hMx : Coordinates.ComplexCoordinates.PowerSeriesHolomorphy.Properties)
    {νp νm ν : Measure SpectralPlane} {Gt : ℝ → ℝ → ℂ}
    (hfp : ∀ c : ℝ, 0 < c → expMoment νp c < ∞)
    (hfm : ∀ c : ℝ, 0 < c → expMoment νm c < ∞)
    (hfin : ∀ c : ℝ, 0 < c → expMoment ν c < ∞)
    (hp : ∀ a b : ℝ, 0 < a → Gt a b = laplaceFourier νp (-b) a)
    (hm : ∀ a b : ℝ, 0 < b → Gt a b = laplaceFourier νm a b)
    (h0 : ∀ t s : ℝ, 0 < t →
      Gt ((t + s) / Real.sqrt 2) ((t - s) / Real.sqrt 2) = laplaceFourier ν s t)
    (hcont : ContinuousOn (fun p : ℝ × ℝ => Gt p.1 p.2) {p | 0 < p.1 ∧ 0 < p.2}) :
    ν {p : SpectralPlane | (p.1 : ℝ) < |p.2|} = 0 := by
  have hsep := isSepHolomorphicOnStrips_expCoordKernel hfp hfm hp hm hcont
  have hA : ∀ (x : Fin 2 → ℝ) (T b : ℝ), 0 ≤ T → 0 ≤ b → b < Real.pi / 2 →
      supOnCross (expCoordKernel Gt) x T b < ∞ := by
    intro x T b _ hb hb'
    have hc : 0 < Real.exp (min (x 0) (x 1) - T) * Real.cos b :=
      mul_pos (Real.exp_pos _) (Real.cos_pos_of_mem_Ioo ⟨by linarith [Real.pi_pos], hb'⟩)
    exact (supOnCross_le hfp hfm hp hm x T b hb hb').trans_lt
      (ENNReal.add_lt_top.2 ⟨hfp _ hc, hfm _ hc⟩)
  obtain ⟨gHat, hhol, hres, hbound⟩ := tubeExtension_two hHull hsep hA
  have hnull : ∀ n n' : ℕ, ν {p : SpectralPlane |
      1 / ((n' : ℝ) + 1) ≤ (1 - 1 / ((n : ℝ) + 2)) * |p.2| - (p.1 : ℝ)} = 0 := by
    intro n n'
    have hε : 0 < 1 / ((n : ℝ) + 2) := by positivity
    have hε' : 1 / ((n : ℝ) + 2) < 1 := by
      rw [div_lt_one (by positivity)]
      have : (0 : ℝ) ≤ n := n.cast_nonneg
      linarith
    have hε₁ : 0 < 1 / ((n' : ℝ) + 1) := by positivity
    obtain ⟨K, hK, hKb⟩ := discRestriction_bounded hfp hfm hp hm hbound hε hε'
    exact measure_eq_zero_of_exp_weighted_le hε₁ (ENNReal.add_lt_top.2 ⟨hK, hK⟩) fun t ht =>
      weighted_mass_le hM hfin h0 (differentiableOn_discRestriction hMx hhol)
        (fun t s hs => discRestriction_ofReal hres hs) hε hε' hKb ht
  have hsub : {p : SpectralPlane | (p.1 : ℝ) < |p.2|} ⊆
      ⋃ n : ℕ, ⋃ n' : ℕ, {p : SpectralPlane |
        1 / ((n' : ℝ) + 1) ≤ (1 - 1 / ((n : ℝ) + 2)) * |p.2| - (p.1 : ℝ)} := by
    intro p hp'
    have hlt : (p.1 : ℝ) < |p.2| := hp'
    set δ := |p.2| - (p.1 : ℝ) with hδ
    have hδ0 : 0 < δ := by linarith
    obtain ⟨n, hn⟩ := exists_nat_gt (2 * |p.2| / δ)
    obtain ⟨n', hn'⟩ := exists_nat_gt (2 / δ)
    refine mem_iUnion.2 ⟨n, mem_iUnion.2 ⟨n', ?_⟩⟩
    show 1 / ((n' : ℝ) + 1) ≤ (1 - 1 / ((n : ℝ) + 2)) * |p.2| - (p.1 : ℝ)
    have h1 : 1 / ((n' : ℝ) + 1) ≤ δ / 2 := by
      rw [div_le_iff₀ (by positivity)]
      rw [div_lt_iff₀ hδ0] at hn'
      nlinarith
    have h2 : |p.2| / ((n : ℝ) + 2) ≤ δ / 2 := by
      rw [div_le_iff₀ (by positivity)]
      rw [div_lt_iff₀ hδ0] at hn
      nlinarith
    have h3 : (1 - 1 / ((n : ℝ) + 2)) * |p.2| = |p.2| - |p.2| / ((n : ℝ) + 2) := by ring
    rw [h3]
    linarith
  exact measure_mono_null hsub
    (measure_iUnion_null fun n => measure_iUnion_null fun n' => hnull n n')
open YangMills.Construction.InfiniteLattice (AmbientSpace)
open YangMills.Construction.PeriodicLattice (coordVec)
theorem planeCoords_rotated (α t s : ℝ) :
    planeCoords (t • planeUnit α + s • planePerp (planeUnit α)) =
      ![t * Real.cos α - s * Real.sin α, t * Real.sin α + s * Real.cos α] := by
  funext i
  fin_cases i <;>
    simp [planeCoords, planeUnit, planePerp, coordVec, PeriodicLattice.coordVec] <;>
    ring
theorem transverseAveragedKernel_rotated_eq {S : (AmbientSpace → ℂ) → (AmbientSpace → ℂ) → ℝ}
    {φ : (Fin 2 → ℝ) → ℂ} {α : ℝ} {ν : Measure SpectralPlane}
    (hs : IsAveragedKernelSpectralMeasure S φ (planeUnit α) ν)
    {t : ℝ} (s : ℝ) (ht : 0 < t) :
    transverseAveragedKernel S φ
        ![t * Real.cos α - s * Real.sin α, t * Real.sin α + s * Real.cos α] =
      laplaceFourier ν s t := by
  lift t to ℝ≥0 using ht.le
  have h := hs.kernel_eq_integral t (NNReal.coe_pos.1 ht) s
  rw [← planeCoords_rotated]
  refine h.trans ?_
  show ∫ p, spectralCharacter t s p ∂ν = ∫ p, laplaceIntegrand s (t : ℝ) p ∂ν
  congr 1
  funext p
  simp only [spectralCharacter, laplaceIntegrand]
  congr 1
  push_cast
  ring
theorem expMoment_lt_top {S : (AmbientSpace → ℂ) → (AmbientSpace → ℂ) → ℝ}
    {φ : (Fin 2 → ℝ) → ℂ} {m : AmbientSpace} {ν : Measure SpectralPlane}
    (hs : IsAveragedKernelSpectralMeasure S φ m ν) {c : ℝ} (hc : 0 < c) :
    expMoment ν c < ∞ :=
  hs.lintegral_decay_lt_top ⟨c, hc.le⟩ (NNReal.coe_pos.1 hc)
theorem vecTwo_congr {a b c d : ℝ} (h₁ : a = c) (h₂ : b = d) :
    (![a, b] : Fin 2 → ℝ) = ![c, d] := by
  rw [h₁, h₂]
theorem div_sqrt_two_eq_mul (x : ℝ) : x / Real.sqrt 2 = x * (Real.sqrt 2 / 2) := by
  have h2 : Real.sqrt 2 * Real.sqrt 2 = 2 := Real.mul_self_sqrt (by norm_num)
  rw [div_eq_iff sqrtTwo_pos.ne']
  linear_combination (-(x / 2)) * h2
theorem spectralSupportInCone_holds (hHull : HolomorphicExtension.TubeExtensionFromStripCross)
    (hM : EuclideanAnalysis.HolomorphicCharFun.ExpMomentsOfHolomorphicCharFun)
    (hMx : Coordinates.ComplexCoordinates.PowerSeriesHolomorphy.Properties)
    (hElem : ReflectionsPlaneFacts.Statement)
    (hPlane : AveragedKernelProperties.Statement) :
    SpectralSupportInCone.Statement := by
  intro St S φ ρ hS hP hφ hρ m
  have hEight : planeReflectionNormals =
      {v | ∃ j : ℤ, v = planeUnit ((j : ℝ) * Real.pi / 4)} :=
    hElem.2.2.2.1.1
  have hmem : ∀ i : ℤ, planeUnit ((i : ℝ) * Real.pi / 4) ∈ planeReflectionNormals :=
    fun i => (Set.ext_iff.1 hEight _).2 ⟨i, rfl⟩
  obtain ⟨j, hj⟩ : ∃ j : ℤ, (m : AmbientSpace) = planeUnit ((j : ℝ) * Real.pi / 4) :=
    (Set.ext_iff.1 hEight _).1 m.2
  have hsp := (hρ.decay ⟨_, hmem (j + 1)⟩).isSpectral
  have hsm := (hρ.decay ⟨_, hmem (j - 1)⟩).isSpectral
  have hs0 := (hρ.decay m).isSpectral
  rw [hj] at hs0
  set θ : ℝ := ((j + 1 : ℤ) : ℝ) * Real.pi / 4 with hθ
  have eθm : ((j - 1 : ℤ) : ℝ) * Real.pi / 4 = θ - Real.pi / 2 := by
    rw [hθ]
    push_cast
    ring
  have eθ0 : (j : ℝ) * Real.pi / 4 = θ - Real.pi / 4 := by
    rw [hθ]
    push_cast
    ring
  simp only [eθm] at hsm
  rw [eθ0] at hs0
  have hkern := (hPlane St S hS hP φ hφ).1.continuousOn
  refine measure_outside_cone_eq_zero hHull hM hMx
    (Gt := fun a b => transverseAveragedKernel S φ
      ![a * Real.cos θ + b * Real.sin θ, a * Real.sin θ - b * Real.cos θ])
    (fun c hc => expMoment_lt_top hsp hc) (fun c hc => expMoment_lt_top hsm hc)
    (fun c hc => expMoment_lt_top hs0 hc) ?_ ?_ ?_ ?_
  · intro a b ha
    rw [← transverseAveragedKernel_rotated_eq hsp (-b) ha]
    exact congrArg _ (vecTwo_congr (by ring) (by ring))
  · intro a b hb
    rw [← transverseAveragedKernel_rotated_eq hsm a hb, Real.cos_sub_pi_div_two,
      Real.sin_sub_pi_div_two]
    exact congrArg _ (vecTwo_congr (by ring) (by ring))
  · intro t s ht
    rw [← transverseAveragedKernel_rotated_eq hs0 s ht, Real.cos_sub, Real.sin_sub,
      Real.cos_pi_div_four, Real.sin_pi_div_four, div_sqrt_two_eq_mul, div_sqrt_two_eq_mul]
    exact congrArg _ (vecTwo_congr (by ring) (by ring))
  · have hmap : Continuous fun p : ℝ × ℝ =>
        (![p.1 * Real.cos θ + p.2 * Real.sin θ, p.1 * Real.sin θ - p.2 * Real.cos θ] :
          Fin 2 → ℝ) := by
      refine continuous_pi fun i => ?_
      rcases fin_two_eq_zero_or_one i with rfl | rfl
      · show Continuous fun p : ℝ × ℝ => p.1 * Real.cos θ + p.2 * Real.sin θ
        fun_prop
      · show Continuous fun p : ℝ × ℝ => p.1 * Real.sin θ - p.2 * Real.cos θ
        fun_prop
    refine hkern.comp hmap.continuousOn ?_
    intro p hp hzero
    have h₀ : p.1 * Real.cos θ + p.2 * Real.sin θ = 0 := congrFun hzero 0
    have h₁ : p.1 * Real.sin θ - p.2 * Real.cos θ = 0 := congrFun hzero 1
    have hsc := Real.sin_sq_add_cos_sq θ
    have hz : p.1 = 0 := by
      linear_combination Real.cos θ * h₀ + Real.sin θ * h₁ - p.1 * hsc
    exact hp.1.ne' hz
end YangMills.Construction.TwoPoints.ConeSupport
end
