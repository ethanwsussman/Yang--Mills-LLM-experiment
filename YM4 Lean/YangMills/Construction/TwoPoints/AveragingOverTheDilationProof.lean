import YangMills.Construction.Splines.CubicSplineBasicFacts
import YangMills.Construction.TwoPoints.AveragingOverTheDilation
import Mathlib
open MeasureTheory Set
set_option autoImplicit false
noncomputable section
namespace YangMills.Construction.TwoPoints.DilationAveraging
open YangMills.Construction.Splines (cubicSpline cubicSplineIntegral CubicSplineFourierFacts
  CubicSplineBasicFacts)
open YangMills.Construction.TwoPoints.TestPlates (averageLowerConst scaledSplineFourier
  scaledFrequency sineLowerConst sineLossConst sineWindowConst)
theorem scaledSplineFourier_eq (hF : CubicSplineFourierFacts) {w k : ℝ} (hw : 0 < w) (hk : 0 < k)
    (q : ℝ) :
    scaledSplineFourier w k q =
      ((1 / 4 * k * w * cubicSplineIntegral * Real.sinc (scaledFrequency w k q) ^ 4 : ℝ) : ℂ) := by
  have ha : (0 : ℝ) < 4 / (k * w) := by positivity
  obtain ⟨a, ha_def⟩ : ∃ a : ℝ, a = 4 / (k * w) := ⟨_, rfl⟩
  rw [← ha_def] at ha
  have hq := hF.1 (k * w * q / 4)
  obtain ⟨g, hg⟩ : ∃ g : ℝ → ℂ, g = fun u : ℝ => (cubicSpline u : ℂ) *
      Complex.exp (Complex.I * (u : ℂ) * ((k * w * q / 4 : ℝ) : ℂ)) := ⟨_, rfl⟩
  have h1 : scaledSplineFourier w k q = ∫ s : ℝ, g (a * s) := by
    unfold scaledSplineFourier
    refine integral_congr_ae (Filter.Eventually.of_forall fun s => ?_)
    show (cubicSpline (4 * s / (k * w)) : ℂ) * Complex.exp (Complex.I * (s : ℂ) * (q : ℂ)) =
      g (a * s)
    have e1 : 4 * s / (k * w) = a * s := by rw [ha_def]; ring
    have e2 : ((a * s : ℝ) : ℂ) * ((k * w * q / 4 : ℝ) : ℂ) = (s : ℂ) * (q : ℂ) := by
      rw [← Complex.ofReal_mul, ← Complex.ofReal_mul]
      congr 1
      rw [ha_def]
      field_simp
    have e3 : Complex.I * ((a * s : ℝ) : ℂ) * ((k * w * q / 4 : ℝ) : ℂ) =
        Complex.I * (s : ℂ) * (q : ℂ) := by
      rw [mul_assoc, e2, mul_assoc]
    rw [hg, e1]
    simp only [e3]
  have h2 : ∫ s : ℝ, g (a * s) = |a⁻¹| • ∫ y : ℝ, g y := Measure.integral_comp_mul_left g a
  have h3 : ∫ y : ℝ, g y =
      (cubicSplineIntegral : ℂ) * ((Real.sinc (k * w * q / 4 / 4) : ℝ) : ℂ) ^ 4 := by
    rw [hg]
    exact hq
  rw [h1, h2, h3, abs_of_pos (inv_pos.mpr ha)]
  have e3 : k * w * q / 4 / 4 = scaledFrequency w k q := by
    unfold scaledFrequency
    ring
  have e4 : a⁻¹ = k * w / 4 := by
    rw [ha_def, inv_div]
  rw [e3, e4, Complex.real_smul]
  push_cast
  ring
theorem sin_one_le_sinc {x : ℝ} (hx : |x| ≤ 1) : Real.sin 1 ≤ Real.sinc x := by
  have key : ∀ y : ℝ, 0 ≤ y → y ≤ 1 → Real.sin 1 ≤ Real.sinc y := by
    intro y hy0 hy1
    rcases hy0.eq_or_lt with h | h
    · rw [← h, Real.sinc_zero]
      exact Real.sin_le_one 1
    · rw [Real.sinc_of_ne_zero h.ne', le_div_iff₀ h]
      have hpi : (1 : ℝ) ≤ Real.pi := by linarith [Real.pi_gt_three]
      have hc := strictConcaveOn_sin_Icc.concaveOn.2
        (left_mem_Icc.mpr Real.pi_pos.le) (mem_Icc.mpr ⟨zero_le_one, hpi⟩)
        (sub_nonneg.mpr hy1) hy0 (by ring)
      simp only [smul_eq_mul, Real.sin_zero, mul_zero, zero_add, mul_one] at hc
      linarith
  rcases le_total 0 x with h | h
  · exact key x h (by rwa [abs_of_nonneg h] at hx)
  · rw [← Real.sinc_neg]
    exact key (-x) (by linarith) (by rwa [abs_of_nonpos h] at hx)
theorem sineLowerConst_pos : 0 < sineLowerConst := by
  have hpi := Real.pi_gt_three
  have hloss : sineLossConst < 1 := by
    have h3 : 1 / Real.pi < 1 / 3 := one_div_lt_one_div_of_lt (by norm_num) hpi
    have e : sineLossConst = 1 / 5 * (2 + 7 / 5 * (1 / Real.pi)) := by
      unfold sineLossConst sineWindowConst YangMills.Construction.TwoPoints.TestPlates.spacingConst
      have : Real.pi ≠ 0 := Real.pi_ne_zero
      field_simp
      ring
    rw [e]
    linarith
  have hs : 0 < Real.sin sineWindowConst := by
    unfold sineWindowConst
    exact Real.sin_pos_of_pos_of_lt_pi (by norm_num) (by linarith)
  unfold sineLowerConst
  exact mul_pos (by linarith) (pow_pos hs 8)
theorem sin_sub_int_mul_pi_pow_eight (x : ℝ) (n : ℤ) :
    Real.sin (x - n * Real.pi) ^ 8 = Real.sin x ^ 8 := by
  rw [Real.sin_sub_int_mul_pi, mul_pow]
  rcases Int.even_or_odd n with h | h
  · rw [h.neg_one_zpow]
    norm_num
  · rw [h.neg_one_zpow]
    norm_num
theorem sin_window_pow_eight_le {x : ℝ} (hfar : ∀ j : ℤ, sineWindowConst ≤ |x - j * Real.pi|) :
    Real.sin sineWindowConst ^ 8 ≤ Real.sin x ^ 8 := by
  have hpi := Real.pi_pos
  obtain ⟨j, hj⟩ : ∃ j : ℤ, j = round (x / Real.pi) := ⟨_, rfl⟩
  have h1 : |x / Real.pi - j| ≤ 1 / 2 := by
    rw [hj]
    exact abs_sub_round _
  have h2 : |x - j * Real.pi| ≤ Real.pi / 2 := by
    have e : x - j * Real.pi = (x / Real.pi - j) * Real.pi := by
      field_simp
    rw [e, abs_mul, abs_of_pos hpi]
    nlinarith
  obtain ⟨y, hy⟩ : ∃ y : ℝ, y = x - j * Real.pi := ⟨_, rfl⟩
  rw [← hy] at h2
  have h3 := hfar j
  rw [← hy] at h3
  have hw : 0 ≤ sineWindowConst := by unfold sineWindowConst; norm_num
  have hs0 : 0 ≤ Real.sin sineWindowConst :=
    Real.sin_nonneg_of_nonneg_of_le_pi hw (by linarith)
  have hs : Real.sin sineWindowConst ≤ Real.sin |y| :=
    Real.sin_le_sin_of_le_of_le_pi_div_two (by linarith) h2 h3
  have e1 : Real.sin |y| ^ 8 = Real.sin y ^ 8 := by
    rcases abs_cases y with ⟨h, _⟩ | ⟨h, _⟩
    · rw [h]
    · rw [h, Real.sin_neg, Even.neg_pow (by decide)]
  rw [← sin_sub_int_mul_pi_pow_eight x j, ← hy, ← e1]
  exact pow_le_pow_left₀ hs0 hs 8
theorem mul_sineLowerConst_le_integral {l : ℝ} (hl : 1 / 2 < l) :
    l * sineLowerConst ≤ ∫ x in l..(2 * l), Real.sin x ^ 8 := by
  have hpi := Real.pi_pos
  have hl0 : 0 < l := by linarith
  have hw : sineWindowConst = 1 / 10 := rfl
  have hw0 : 0 < sineWindowConst := by rw [hw]; norm_num
  obtain ⟨a, ha⟩ : ∃ a : ℝ, a = (l - sineWindowConst) / Real.pi := ⟨_, rfl⟩
  obtain ⟨b, hb⟩ : ∃ b : ℝ, b = (2 * l + sineWindowConst) / Real.pi := ⟨_, rfl⟩
  have hab : a < b := by
    rw [ha, hb]
    exact div_lt_div_of_pos_right (by linarith) hpi
  obtain ⟨J, hJ⟩ : ∃ J : Finset ℤ, J = Finset.Icc ⌈a⌉ ⌊b⌋ := ⟨_, rfl⟩
  have hcard : (J.card : ℝ) ≤ 1 + (b - a) := by
    have hnn : 0 ≤ ⌊b⌋ + 1 - ⌈a⌉ := by
      have : ⌈a⌉ ≤ ⌊b⌋ + 1 := by
        apply Int.ceil_le.mpr
        push_cast
        linarith [Int.lt_floor_add_one b]
      omega
    have h' : ((J.card : ℤ) : ℝ) = ((⌊b⌋ + 1 - ⌈a⌉ : ℤ) : ℝ) := by
      rw [hJ, Int.card_Icc, Int.toNat_of_nonneg hnn]
    have h'' : (J.card : ℝ) = ((J.card : ℤ) : ℝ) := by simp
    rw [h'', h']
    push_cast
    linarith [Int.floor_le b, Int.le_ceil a]
  obtain ⟨U, hU⟩ : ∃ U : Set ℝ, U = ⋃ j ∈ J,
      Ioo ((j : ℝ) * Real.pi - sineWindowConst) ((j : ℝ) * Real.pi + sineWindowConst) := ⟨_, rfl⟩
  have hUm : MeasurableSet U := by
    rw [hU]
    exact Finset.measurableSet_biUnion _ (fun _ _ => measurableSet_Ioo)
  have hUvol : volume U ≤ ENNReal.ofReal (2 * sineWindowConst * J.card) := by
    rw [hU]
    refine (measure_biUnion_finset_le J _).trans ?_
    simp only [Real.volume_Ioo]
    have hconst : ∀ j ∈ J, ENNReal.ofReal ((j : ℝ) * Real.pi + sineWindowConst -
        ((j : ℝ) * Real.pi - sineWindowConst)) = ENNReal.ofReal (2 * sineWindowConst) := by
      intro j _
      congr 1
      ring
    rw [Finset.sum_congr rfl hconst, Finset.sum_const, nsmul_eq_mul,
      mul_comm (2 * sineWindowConst), ENNReal.ofReal_mul (Nat.cast_nonneg _), ENNReal.ofReal_natCast]
  obtain ⟨S, hS⟩ : ∃ S : Set ℝ, S = Ioc l (2 * l) \ U := ⟨_, rfl⟩
  have hSsub : S ⊆ Ioc l (2 * l) := by
    rw [hS]
    exact sdiff_subset
  have hSm : MeasurableSet S := by
    rw [hS]
    exact measurableSet_Ioc.diff hUm
  have hfar : ∀ x ∈ S, Real.sin sineWindowConst ^ 8 ≤ Real.sin x ^ 8 := by
    intro x hx
    rw [hS] at hx
    refine sin_window_pow_eight_le fun j => ?_
    by_contra hlt
    rw [not_le, abs_lt] at hlt
    apply hx.2
    rw [hU]
    refine mem_iUnion₂.mpr ⟨j, ?_, ?_⟩
    · rw [hJ, Finset.mem_Icc]
      refine ⟨Int.ceil_le.mpr ?_, Int.le_floor.mpr ?_⟩
      · rw [ha, div_le_iff₀ hpi]
        linarith [hx.1.1, hlt.2]
      · rw [hb, le_div_iff₀ hpi]
        linarith [hx.1.2, hlt.1]
    · exact ⟨by linarith [hlt.2], by linarith [hlt.1]⟩
  have hvol : ENNReal.ofReal l ≤ volume S + volume U := by
    calc ENNReal.ofReal l = volume (Ioc l (2 * l)) := by
          rw [Real.volume_Ioc]
          congr 1
          ring
      _ ≤ volume (S ∪ U) := by
          refine measure_mono fun x hx => ?_
          by_cases hxU : x ∈ U
          · exact Or.inr hxU
          · exact Or.inl (by rw [hS]; exact ⟨hx, hxU⟩)
      _ ≤ volume S + volume U := measure_union_le _ _
  have hSfin : volume S ≠ ⊤ := by
    refine ((measure_mono hSsub).trans_lt ?_).ne
    rw [Real.volume_Ioc]
    exact ENNReal.ofReal_lt_top
  have ht : 0 ≤ 2 * sineWindowConst * (J.card : ℝ) := by positivity
  have hreal : l - 2 * sineWindowConst * J.card ≤ (volume S).toReal := by
    have h1 : ENNReal.ofReal l ≤ volume S + ENNReal.ofReal (2 * sineWindowConst * J.card) :=
      hvol.trans (by gcongr)
    have h2 := ENNReal.toReal_mono (ENNReal.add_ne_top.mpr ⟨hSfin, ENNReal.ofReal_ne_top⟩) h1
    rw [ENNReal.toReal_add hSfin ENNReal.ofReal_ne_top, ENNReal.toReal_ofReal hl0.le,
      ENNReal.toReal_ofReal ht] at h2
    linarith
  have hcont : Continuous fun x : ℝ => Real.sin x ^ 8 := Real.continuous_sin.pow 8
  have hInt : IntegrableOn (fun x : ℝ => Real.sin x ^ 8) (Ioc l (2 * l)) :=
    hcont.integrableOn_Ioc
  have hs8 : 0 ≤ Real.sin sineWindowConst ^ 8 := by positivity
  have step1 : ∫ x in S, Real.sin x ^ 8 ≤ ∫ x in Ioc l (2 * l), Real.sin x ^ 8 :=
    setIntegral_mono_set hInt (Filter.Eventually.of_forall fun x => by
      show (0 : ℝ) ≤ Real.sin x ^ 8
      positivity) (LE.le.eventuallyLE hSsub)
  have step2 : (volume S).toReal * Real.sin sineWindowConst ^ 8 ≤ ∫ x in S, Real.sin x ^ 8 := by
    have h := setIntegral_mono_on (μ := volume) (s := S)
      (f := fun _ : ℝ => Real.sin sineWindowConst ^ 8)
      (g := fun x : ℝ => Real.sin x ^ 8)
      ((continuous_const.integrableOn_Ioc).mono_set hSsub) (hInt.mono_set hSsub) hSm hfar
    simpa [setIntegral_const, smul_eq_mul, Measure.real] using h
  have hloss : 2 * sineWindowConst * (1 + (b - a)) ≤ l * sineLossConst := by
    obtain ⟨p, hp⟩ : ∃ p : ℝ, p = 1 / Real.pi := ⟨_, rfl⟩
    have hp0 : 0 < p := by rw [hp]; positivity
    have e1 : sineLossConst = 1 / 5 * (2 + 7 / 5 * p) := by
      unfold sineLossConst
      rw [hw, hp]
      unfold YangMills.Construction.TwoPoints.TestPlates.spacingConst
      field_simp
      ring
    have e2 : b - a = (l + 1 / 5) * p := by
      rw [ha, hb, hw, hp]
      field_simp
      ring
    rw [e1, e2, hw]
    nlinarith [mul_nonneg (by linarith : 0 ≤ 2 * l - 1) hp0.le]
  have hlast : l * (1 - sineLossConst) ≤ (volume S).toReal := by
    have := mul_le_mul_of_nonneg_left hcard (by positivity : 0 ≤ 2 * sineWindowConst)
    nlinarith
  rw [intervalIntegral.integral_of_le (by linarith)]
  calc l * sineLowerConst = l * (1 - sineLossConst) * Real.sin sineWindowConst ^ 8 := by
        unfold sineLowerConst
        ring
    _ ≤ (volume S).toReal * Real.sin sineWindowConst ^ 8 := mul_le_mul_of_nonneg_right hlast hs8
    _ ≤ ∫ x in S, Real.sin x ^ 8 := step2
    _ ≤ _ := step1
theorem min_mul_le_integral_sinc_pow_eight {w : ℝ} (hw : 0 < w) (q : ℝ) :
    min (Real.sin 1 ^ 8) (8 ^ 8 * sineLowerConst) * (1 + w ^ 2 * q ^ 2) ^ (-4 : ℤ) ≤
      ∫ k in (1 : ℝ)..2, Real.sinc (scaledFrequency w k q) ^ 8 := by
  have hx : Continuous fun k : ℝ => scaledFrequency w k q := by
    unfold scaledFrequency
    fun_prop
  have hcont : Continuous fun k : ℝ => Real.sinc (scaledFrequency w k q) ^ 8 :=
    (Real.continuous_sinc.comp hx).pow 8
  have hsin1 : 0 < Real.sin 1 :=
    Real.sin_pos_of_pos_of_lt_pi one_pos (by linarith [Real.pi_gt_three])
  have hD : 0 < 1 + w ^ 2 * q ^ 2 := by positivity
  have hD4 : 0 < (1 + w ^ 2 * q ^ 2) ^ 4 := pow_pos hD 4
  obtain ⟨W, hW⟩ : ∃ W : ℝ, W = ((1 + w ^ 2 * q ^ 2) ^ 4)⁻¹ := ⟨_, rfl⟩
  have hWz : (1 + w ^ 2 * q ^ 2) ^ (-4 : ℤ) = W := by
    rw [hW, zpow_neg]
    norm_cast
  rw [hWz]
  have hW0 : 0 ≤ W := by
    rw [hW]
    positivity
  have hW1 : W ≤ 1 := by
    rw [hW]
    refine inv_le_one_of_one_le₀ (one_le_pow₀ ?_)
    nlinarith [mul_nonneg (sq_nonneg w) (sq_nonneg q)]
  by_cases hc : |w * q| ≤ 8
  · have hpt : ∀ k ∈ Icc (1 : ℝ) 2,
        Real.sin 1 ^ 8 ≤ Real.sinc (scaledFrequency w k q) ^ 8 := by
      intro k hk
      refine pow_le_pow_left₀ hsin1.le (sin_one_le_sinc ?_) 8
      have e : scaledFrequency w k q = k * (w * q) / 16 := by
        unfold scaledFrequency
        ring
      have hk0 : 0 < k := by linarith [hk.1]
      rw [e, abs_div, abs_mul, abs_of_pos hk0, abs_of_pos (by norm_num : (0 : ℝ) < 16),
        div_le_one (by norm_num)]
      nlinarith [hk.2, abs_nonneg (w * q)]
    have hI := intervalIntegral.integral_mono_on (μ := volume) (a := 1) (b := 2) (by norm_num)
      (intervalIntegrable_const (μ := volume) (c := Real.sin 1 ^ 8)) (hcont.intervalIntegrable _ _)
      hpt
    rw [intervalIntegral.integral_const] at hI
    have h1 : min (Real.sin 1 ^ 8) (8 ^ 8 * sineLowerConst) * W ≤ Real.sin 1 ^ 8 * 1 :=
      mul_le_mul (min_le_left _ _) hW1 hW0 (pow_pos hsin1 8).le
    norm_num at hI
    linarith
  · have hqne : 0 < |q| := by
      rcases eq_or_ne q 0 with h | h
      · exfalso
        apply hc
        rw [h]
        norm_num
      · exact abs_pos.mpr h
    obtain ⟨l, hl⟩ : ∃ l : ℝ, l = w * |q| / 16 := ⟨_, rfl⟩
    have hl2 : 1 / 2 < l := by
      have h8 : 8 < |w * q| := not_le.mp hc
      rw [abs_mul, abs_of_pos hw] at h8
      rw [hl]
      linarith
    have hl0 : 0 < l := by linarith
    have hP : 0 < (2 * l) ^ 8 := by positivity
    have hpt : ∀ k ∈ Icc (1 : ℝ) 2, ((2 * l) ^ 8)⁻¹ * Real.sin (k * l) ^ 8 ≤
        Real.sinc (scaledFrequency w k q) ^ 8 := by
      intro k hk
      have hk0 : 0 < k := by linarith [hk.1]
      have hkl : 0 < k * l := mul_pos hk0 hl0
      have e : Real.sinc (scaledFrequency w k q) = Real.sinc (k * l) := by
        rcases abs_cases q with ⟨h, _⟩ | ⟨h, _⟩
        · congr 1
          unfold scaledFrequency
          rw [hl, h]
          ring
        · rw [← Real.sinc_neg (k * l)]
          congr 1
          unfold scaledFrequency
          rw [hl, h]
          ring
      rw [e, Real.sinc_of_ne_zero hkl.ne', div_pow, inv_mul_eq_div]
      refine div_le_div_of_nonneg_left (by positivity) (pow_pos hkl 8) ?_
      refine pow_le_pow_left₀ hkl.le ?_ 8
      nlinarith [hk.2]
    have hcs : Continuous fun k : ℝ => ((2 * l) ^ 8)⁻¹ * Real.sin (k * l) ^ 8 := by
      fun_prop
    have hI := intervalIntegral.integral_mono_on (μ := volume) (a := 1) (b := 2) (by norm_num)
      (hcs.intervalIntegrable _ _) (hcont.intervalIntegrable _ _) hpt
    rw [intervalIntegral.integral_const_mul,
      intervalIntegral.integral_comp_mul_right (fun y : ℝ => Real.sin y ^ 8) hl0.ne', one_mul,
      smul_eq_mul] at hI
    have hJ := mul_sineLowerConst_le_integral hl2
    have hfl : sineLowerConst ≤ l⁻¹ * ∫ x in l..(2 * l), Real.sin x ^ 8 := by
      rw [inv_mul_eq_div, le_div_iff₀ hl0]
      linarith
    have hP8 : (2 * l) ^ 8 * 8 ^ 8 = (w ^ 2 * q ^ 2) ^ 4 := by
      rw [hl]
      have hq2 : q ^ 2 = |q| ^ 2 := (sq_abs q).symm
      rw [hq2]
      ring
    have hle : (w ^ 2 * q ^ 2) ^ 4 ≤ (1 + w ^ 2 * q ^ 2) ^ 4 :=
      pow_le_pow_left₀ (by positivity) (by linarith) 4
    have hWP : 8 ^ 8 * W ≤ ((2 * l) ^ 8)⁻¹ := by
      rw [hW, ← div_eq_mul_inv, div_le_iff₀ hD4, inv_mul_eq_div, le_div_iff₀ hP]
      linarith
    have hs := sineLowerConst_pos
    calc min (Real.sin 1 ^ 8) (8 ^ 8 * sineLowerConst) * W ≤ 8 ^ 8 * sineLowerConst * W :=
          mul_le_mul_of_nonneg_right (min_le_right _ _) hW0
      _ = sineLowerConst * (8 ^ 8 * W) := by ring
      _ ≤ sineLowerConst * ((2 * l) ^ 8)⁻¹ := mul_le_mul_of_nonneg_left hWP hs.le
      _ ≤ (l⁻¹ * ∫ x in l..(2 * l), Real.sin x ^ 8) * ((2 * l) ^ 8)⁻¹ :=
          mul_le_mul_of_nonneg_right hfl (by positivity)
      _ ≤ _ := by
          refine le_trans (le_of_eq ?_) hI
          ring
theorem statement_holds (h : CubicSplineBasicFacts) : Statement := by
  obtain ⟨-, -, hF, -⟩ := h
  have hc : 0 < cubicSplineIntegral := hF.2.2
  have hsin1 : 0 < Real.sin 1 :=
    Real.sin_pos_of_pos_of_lt_pi one_pos (by linarith [Real.pi_gt_three])
  refine ⟨?_, fun w hw => ⟨?_, ?_, ?_, ?_⟩⟩
  · unfold averageLowerConst
    exact mul_pos (mul_pos (by norm_num) (pow_pos hc 2))
      (lt_min (pow_pos hsin1 8) (mul_pos (by norm_num) sineLowerConst_pos))
  · intro q
    have hx : Continuous fun k : ℝ => scaledFrequency w k q := by
      unfold scaledFrequency
      fun_prop
    have hs : Continuous fun k : ℝ => Real.sinc (scaledFrequency w k q) :=
      Real.continuous_sinc.comp hx
    have hform : EqOn (fun k : ℝ => (scaledSplineFourier w k q).re ^ 2)
        (fun k : ℝ => (1 / 4 * k * w * cubicSplineIntegral *
          Real.sinc (scaledFrequency w k q) ^ 4) ^ 2) (uIcc 1 2) := by
      intro k hk
      rw [uIcc_of_le (by norm_num)] at hk
      show (scaledSplineFourier w k q).re ^ 2 = _
      rw [scaledSplineFourier_eq hF hw (by linarith [hk.1]) q, Complex.ofReal_re]
    rw [intervalIntegral.integral_congr hform]
    have hpt : ∀ k ∈ Icc (1 : ℝ) 2, w ^ 2 * cubicSplineIntegral ^ 2 / 16 *
        Real.sinc (scaledFrequency w k q) ^ 8 ≤
        (1 / 4 * k * w * cubicSplineIntegral * Real.sinc (scaledFrequency w k q) ^ 4) ^ 2 := by
      intro k hk
      have hk2 : 1 ≤ k ^ 2 := by nlinarith [hk.1]
      have e : (1 / 4 * k * w * cubicSplineIntegral * Real.sinc (scaledFrequency w k q) ^ 4) ^ 2 =
          w ^ 2 * cubicSplineIntegral ^ 2 / 16 * Real.sinc (scaledFrequency w k q) ^ 8 * k ^ 2 := by
        ring
      rw [e]
      exact le_mul_of_one_le_right (by positivity) hk2
    have c1 : Continuous fun k : ℝ => w ^ 2 * cubicSplineIntegral ^ 2 / 16 *
        Real.sinc (scaledFrequency w k q) ^ 8 := continuous_const.mul (hs.pow 8)
    have c2 : Continuous fun k : ℝ => (1 / 4 * k * w * cubicSplineIntegral *
        Real.sinc (scaledFrequency w k q) ^ 4) ^ 2 :=
      ((((continuous_const.mul continuous_id).mul continuous_const).mul
        continuous_const).mul (hs.pow 4)).pow 2
    have hI := intervalIntegral.integral_mono_on (μ := volume) (a := 1) (b := 2) (by norm_num)
      (c1.intervalIntegrable _ _) (c2.intervalIntegrable _ _) hpt
    rw [intervalIntegral.integral_const_mul] at hI
    refine le_trans ?_ hI
    have hm := mul_le_mul_of_nonneg_left (min_mul_le_integral_sinc_pow_eight hw q)
      (by positivity : 0 ≤ w ^ 2 * cubicSplineIntegral ^ 2 / 16)
    refine le_trans (le_of_eq ?_) hm
    unfold averageLowerConst
    ring
  · intro q k hk
    exact scaledSplineFourier_eq hF hw (by linarith [hk.1]) q
  · intro q k hk
    rw [scaledSplineFourier_eq hF hw (by linarith [hk.1]) q]
    exact Complex.ofReal_im _
  · have hx : Continuous fun p : ℝ × ℝ => scaledFrequency w p.1 p.2 := by
      unfold scaledFrequency
      fun_prop
    have hs : Continuous fun p : ℝ × ℝ => Real.sinc (scaledFrequency w p.1 p.2) :=
      Real.continuous_sinc.comp hx
    have hf : ContinuousOn (fun p : ℝ × ℝ => ((1 / 4 * p.1 * w * cubicSplineIntegral *
        Real.sinc (scaledFrequency w p.1 p.2) ^ 4 : ℝ) : ℂ)) (Icc (1 : ℝ) 2 ×ˢ univ) :=
      (Complex.continuous_ofReal.comp ((((continuous_const.mul continuous_fst).mul
        continuous_const).mul continuous_const).mul (hs.pow 4))).continuousOn
    exact hf.congr fun p hp => scaledSplineFourier_eq hF hw (by linarith [hp.1.1]) p.2
end YangMills.Construction.TwoPoints.DilationAveraging
