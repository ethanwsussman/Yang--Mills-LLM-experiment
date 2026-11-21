import YangMills.Construction.ClusterExpansionOfAStep.FactorOfAClassIsOneRuleProof
import YangMills.Construction.ColdStepAtMirrorFrames.MomentsOfAConvexMeasure
import YangMills.Construction.ColdStepAtMirrorFrames.RimOfACutProof
import YangMills.Construction.SummableBoundsOfTheFlow.LawOfACutIsAProbability
import YangMills.Construction.SummableBoundsOfTheFlow.MeanAlongAField
import YangMills.Construction.SummableBoundsOfTheFlow.PowersOfACutProof
import YangMills.Construction.SummableBoundsOfTheFlow.RimMomentsOfALaw
import Mathlib
set_option autoImplicit false
noncomputable section
open MeasureTheory
open scoped ContDiff
namespace YangMills.Construction.Estimates
open YangMills.Construction.ColdStepAtMirrorFrames YangMills.Construction.BondIntegration YangMills.Construction.ConvexObservables
variable {ρ : ℝ} {p : ℝ → ℝ}
private def clampedSlope (ρ : ℝ) (p : ℝ → ℝ) (u : ℝ) : ℝ := if u ≤ ρ / 2 then 0 else deriv p u
private theorem iteratedDeriv_contDiffOn (hp : IsCutoff ρ p) (j : ℕ) :
    ContDiffOn ℝ ∞ (iteratedDeriv j p) (Set.Ioo 0 ρ) := by apply _root_.YangMills.SharedProofs.p62039 <;> assumption
private theorem clampedSlope_eq_zero (hC : cutoffDerivBoundsStatement) (hρ : 0 < ρ) (hp : IsCutoff ρ p) {u : ℝ}
    (hu : u < 5 * ρ / 8) : clampedSlope ρ p u = 0 := by
  unfold clampedSlope
  split_ifs with h
  · rfl
  · push Not at h
    have := (hC ρ p hρ hp).2.1 u (by linarith) hu 1 le_rfl
    rwa [iteratedDeriv_one] at this
private theorem clampedSlope_eq_deriv {u : ℝ} (hu : ρ / 2 < u) : clampedSlope ρ p u = deriv p u := by
  unfold clampedSlope
  rw [if_neg (not_le.2 hu)]
private theorem clampedSlope_nonneg (hC : cutoffDerivBoundsStatement) (hρ : 0 < ρ) (hp : IsCutoff ρ p) {u : ℝ}
    (hu : u < ρ) : 0 ≤ clampedSlope ρ p u := by
  unfold clampedSlope
  split_ifs with h
  · exact le_rfl
  · push Not at h
    exact (hC ρ p hρ hp).1 u (by linarith) hu
private def slopePowBump (ρ : ℝ) (p : ℝ → ℝ) (q : ℕ) (u : ℝ) : ℝ :=
  clampedSlope ρ p u ^ q * cutoffFactor ρ p u
private theorem clampedSlope_contDiffAt (hC : cutoffDerivBoundsStatement) (hρ : 0 < ρ) (hp : IsCutoff ρ p)
    {u : ℝ} (hu : u < ρ) : ContDiffAt ℝ ∞ (clampedSlope ρ p) u := by
  by_cases h : u < 5 * ρ / 8
  · have hev : clampedSlope ρ p =ᶠ[nhds u] fun _ => 0 := by
      filter_upwards [Iio_mem_nhds h] with v hv
      exact clampedSlope_eq_zero hC hρ hp hv
    exact contDiffAt_const.congr_of_eventuallyEq hev
  · push Not at h
    have h1 : ρ / 2 < u := by linarith
    have hev : clampedSlope ρ p =ᶠ[nhds u] deriv p := by
      filter_upwards [Ioi_mem_nhds h1] with v hv
      exact clampedSlope_eq_deriv hv
    refine ContDiffAt.congr_of_eventuallyEq ?_ hev
    have h2 := (iteratedDeriv_contDiffOn hp 1).contDiffAt (Ioo_mem_nhds (by linarith : 0 < u) hu)
    simpa [iteratedDeriv_one] using h2
private theorem cutoffFactor_of_lt {u : ℝ} (hu : u < ρ) : cutoffFactor ρ p u = Real.exp (-p u) := by
  unfold cutoffFactor; rw [if_pos hu]
private theorem cutoffFactor_of_le {u : ℝ} (hu : ρ ≤ u) : cutoffFactor ρ p u = 0 := by
  unfold cutoffFactor; rw [if_neg (not_lt.2 hu)]
private theorem slopePowBump_eq_zero_of_lt (hC : cutoffDerivBoundsStatement) (hρ : 0 < ρ) (hp : IsCutoff ρ p)
    {q : ℕ} (hq : 1 ≤ q) {u : ℝ} (hu : u < 5 * ρ / 8) : slopePowBump ρ p q u = 0 := by
  unfold slopePowBump
  rw [clampedSlope_eq_zero hC hρ hp hu, zero_pow (by omega), zero_mul]
private theorem slopePowBump_eq_zero_of_le {q : ℕ} {u : ℝ} (hu : ρ ≤ u) : slopePowBump ρ p q u = 0 := by
  unfold slopePowBump
  rw [cutoffFactor_of_le hu, mul_zero]
private theorem hasDerivAt_deriv_of_isCutoff (hp : IsCutoff ρ p) {u : ℝ} (h0 : 0 < u) (h1 : u < ρ) :
    HasDerivAt (deriv p) (deriv (deriv p) u) u := by apply _root_.YangMills.Construction.ColdStepAtMirrorFrames.CutoffFactor.cutoff_hasDerivAt_deriv <;> assumption
private theorem hasDerivAt_of_isCutoff (hp : IsCutoff ρ p) {u : ℝ} (h0 : 0 < u) (h1 : u < ρ) :
    HasDerivAt p (deriv p u) u := by apply _root_.YangMills.Construction.ColdStepAtMirrorFrames.CutoffFactor.cutoff_hasDerivAt <;> assumption
private theorem slopePowBump_hasDerivAt (hp : IsCutoff ρ p) (hρ : 0 < ρ) (q : ℕ) {u : ℝ} (h0 : ρ / 2 < u)
    (h1 : u < ρ) :
    HasDerivAt (slopePowBump ρ p q)
      (((q : ℝ) * deriv p u ^ (q - 1) * deriv (deriv p) u - deriv p u ^ (q + 1)) * Real.exp (-p u)) u := by
  have hu0 : 0 < u := by linarith
  have hev : slopePowBump ρ p q =ᶠ[nhds u] fun v => deriv p v ^ q * Real.exp (-p v) := by
    filter_upwards [Ioo_mem_nhds h0 h1] with v hv
    unfold slopePowBump
    rw [clampedSlope_eq_deriv hv.1, cutoffFactor_of_lt hv.2]
  refine HasDerivAt.congr_of_eventuallyEq ?_ hev
  have h2 := (hasDerivAt_deriv_of_isCutoff hp hu0 h1).fun_pow q
  have h3 := ((hasDerivAt_of_isCutoff hp hu0 h1).fun_neg).exp
  have h4 := h2.fun_mul h3
  refine h4.congr_deriv ?_
  ring
private theorem slopePowBump_bounds (hC : cutoffDerivBoundsStatement) (hp : IsCutoff ρ p) (hρ : 0 < ρ) (q : ℕ) :
    ∃ B : ℝ, 0 ≤ B ∧ ∀ u, ρ / 2 < u → u < ρ → |slopePowBump ρ p q u| ≤ B * (ρ - u) ^ 2 ∧
      |((q : ℝ) * deriv p u ^ (q - 1) * deriv (deriv p) u - deriv p u ^ (q + 1)) * Real.exp (-p u)| ≤
        B * (ρ - u) := by
  obtain ⟨hnn, -, hpow, -, hder, D, hD0, hD⟩ := hC ρ p hρ hp
  obtain ⟨C₂, k₂, hC₂, h2⟩ := hder 2 (by norm_num)
  obtain ⟨C₃, hC₃, h3⟩ := hpow (q + 1 + k₂ + 1)
  obtain ⟨C₄, hC₄, h4⟩ := hpow (q + 2)
  refine ⟨C₄ * D ^ 2 + ((q : ℝ) * C₂ + 1) * C₃ * D, by positivity, fun u hu1 hu2 => ?_⟩
  have hu0 : 0 < u := by linarith
  have hP := hnn u hu0 hu2
  set P := deriv p u with hPd
  set e := Real.exp (-p u) with he
  have he0 : 0 < e := Real.exp_pos _
  have hr : 0 < ρ - u := by linarith
  have hinv : 1 ≤ D * (ρ - u) * (1 + P) := by
    have h5 := hD u hu0 hu2
    have h6 : (ρ - u)⁻¹ * (ρ - u) = 1 := inv_mul_cancel₀ hr.ne'
    nlinarith [mul_le_mul_of_nonneg_right h5 hr.le]
  have hone : (1 : ℝ) ≤ 1 + P := by linarith
  have hX : 0 ≤ D * (ρ - u) := by positivity
  constructor
  · have e1 : slopePowBump ρ p q u = P ^ q * e := by
      unfold slopePowBump
      rw [clampedSlope_eq_deriv hu1, cutoffFactor_of_lt hu2]
    rw [e1, abs_of_nonneg (by positivity)]
    have h5 := h4 u hu0 hu2
    have h6 : P ^ q ≤ (1 + P) ^ q := pow_le_pow_left₀ hP (by linarith) q
    have h7 : 1 ≤ (D * (ρ - u) * (1 + P)) ^ 2 := one_le_pow₀ hinv
    calc P ^ q * e ≤ (1 + P) ^ q * e * 1 := by rw [mul_one]; gcongr
      _ ≤ (1 + P) ^ q * e * (D * (ρ - u) * (1 + P)) ^ 2 := by gcongr
      _ = (1 + P) ^ (q + 2) * e * (D ^ 2 * (ρ - u) ^ 2) := by ring
      _ ≤ C₄ * (D ^ 2 * (ρ - u) ^ 2) := by gcongr
      _ ≤ _ := by
          have : 0 ≤ ((q : ℝ) * C₂ + 1) * C₃ * D * (ρ - u) ^ 2 := by positivity
          nlinarith
  · rw [abs_mul, abs_of_pos he0]
    have h5 := h2 u hu0 hu2
    have e2 : iteratedDeriv 2 p = deriv (deriv p) := by
      rw [iteratedDeriv_succ, iteratedDeriv_one]
    rw [e2] at h5
    set P2 := deriv (deriv p) u with hP2
    have h6 : |(q : ℝ) * P ^ (q - 1) * P2 - P ^ (q + 1)| ≤ ((q : ℝ) * C₂ + 1) * (1 + P) ^ (q + 1 + k₂) := by
      have a1 : P ^ (q - 1) ≤ (1 + P) ^ (q + 1) := by
        calc P ^ (q - 1) ≤ (1 + P) ^ (q - 1) := pow_le_pow_left₀ hP (by linarith) _
          _ ≤ (1 + P) ^ (q + 1) := pow_le_pow_right₀ hone (by omega)
      have a2 : P ^ (q + 1) ≤ (1 + P) ^ (q + 1 + k₂) := by
        calc P ^ (q + 1) ≤ (1 + P) ^ (q + 1) := pow_le_pow_left₀ hP (by linarith) _
          _ ≤ (1 + P) ^ (q + 1 + k₂) := pow_le_pow_right₀ hone (by omega)
      calc |(q : ℝ) * P ^ (q - 1) * P2 - P ^ (q + 1)|
          ≤ |(q : ℝ) * P ^ (q - 1) * P2| + |P ^ (q + 1)| := abs_sub _ _
        _ = (q : ℝ) * P ^ (q - 1) * |P2| + P ^ (q + 1) := by
            rw [abs_mul, abs_mul, abs_of_nonneg (by positivity : (0 : ℝ) ≤ q),
              abs_of_nonneg (by positivity : 0 ≤ P ^ (q - 1)), abs_of_nonneg (by positivity : 0 ≤ P ^ (q + 1))]
        _ ≤ (q : ℝ) * (1 + P) ^ (q + 1) * (C₂ * (1 + P) ^ k₂) + (1 + P) ^ (q + 1 + k₂) := by gcongr
        _ = _ := by ring
    have h7 := h3 u hu0 hu2
    calc |(q : ℝ) * P ^ (q - 1) * P2 - P ^ (q + 1)| * e
        ≤ ((q : ℝ) * C₂ + 1) * (1 + P) ^ (q + 1 + k₂) * e * 1 := by rw [mul_one]; gcongr
      _ ≤ ((q : ℝ) * C₂ + 1) * (1 + P) ^ (q + 1 + k₂) * e * (D * (ρ - u) * (1 + P)) := by gcongr
      _ = ((q : ℝ) * C₂ + 1) * ((1 + P) ^ (q + 1 + k₂ + 1) * e) * (D * (ρ - u)) := by ring
      _ ≤ ((q : ℝ) * C₂ + 1) * C₃ * (D * (ρ - u)) := by gcongr
      _ ≤ _ := by
          have : 0 ≤ C₄ * D ^ 2 * (ρ - u) := by positivity
          nlinarith
private theorem slopePowBump_contDiff (hC : cutoffDerivBoundsStatement) (hp : IsCutoff ρ p) (hρ : 0 < ρ) {q : ℕ}
    (hq : 1 ≤ q) : ContDiff ℝ 1 (slopePowBump ρ p q) := by
  obtain ⟨B, hB0, hB⟩ := slopePowBump_bounds hC hp hρ q
  have hlow : ∀ u, u < 5 * ρ / 8 → slopePowBump ρ p q =ᶠ[nhds u] fun _ => 0 := fun u hu => by
    filter_upwards [Iio_mem_nhds hu] with v hv
    exact slopePowBump_eq_zero_of_lt hC hρ hp hq hv
  have hhigh : ∀ u, ρ < u → slopePowBump ρ p q =ᶠ[nhds u] fun _ => 0 := fun u hu => by
    filter_upwards [Ioi_mem_nhds hu] with v hv
    exact slopePowBump_eq_zero_of_le (le_of_lt hv)
  have hatρ : HasDerivAt (slopePowBump ρ p q) 0 ρ := by
    rw [hasDerivAt_iff_isLittleO, Asymptotics.isLittleO_iff]
    intro c hc
    have hball : Metric.ball ρ (min (ρ / 2) (c / (B + 1))) ∈ nhds ρ := Metric.ball_mem_nhds _ (by positivity)
    filter_upwards [hball] with x hx
    have h1 : |x - ρ| < min (ρ / 2) (c / (B + 1)) := by simpa [Real.dist_eq] using hx
    have h2 : |x - ρ| < ρ / 2 := lt_of_lt_of_le h1 (min_le_left _ _)
    have h3 : |x - ρ| < c / (B + 1) := lt_of_lt_of_le h1 (min_le_right _ _)
    rw [lt_div_iff₀ (by positivity)] at h3
    simp only [slopePowBump_eq_zero_of_le (le_refl ρ), sub_zero, smul_zero, Real.norm_eq_abs]
    by_cases hx2 : x < ρ
    · have h4 := (hB x (by rw [abs_lt] at h2; linarith) hx2).1
      have h5 : (ρ - x) ^ 2 = |x - ρ| * |x - ρ| := by rw [abs_mul_abs_self]; ring
      rw [h5] at h4
      have h6 := abs_nonneg (x - ρ)
      nlinarith
    · rw [slopePowBump_eq_zero_of_le (not_lt.1 hx2), abs_zero]
      positivity
  have hdiff : ∀ u, HasDerivAt (slopePowBump ρ p q) (deriv (slopePowBump ρ p q) u) u := by
    intro u
    apply DifferentiableAt.hasDerivAt
    by_cases h1 : u < 5 * ρ / 8
    · exact (differentiableAt_const (0 : ℝ)).congr_of_eventuallyEq (hlow u h1)
    · push Not at h1
      rcases lt_trichotomy u ρ with h2 | h2 | h2
      · exact (slopePowBump_hasDerivAt hp hρ q (by linarith) h2).differentiableAt
      · rw [h2]; exact hatρ.differentiableAt
      · exact (differentiableAt_const (0 : ℝ)).congr_of_eventuallyEq (hhigh u h2)
  rw [contDiff_one_iff_deriv]
  refine ⟨fun u => (hdiff u).differentiableAt, ?_⟩
  rw [continuous_iff_continuousAt]
  intro u
  by_cases h1 : u < 5 * ρ / 8
  · have : deriv (slopePowBump ρ p q) =ᶠ[nhds u] fun _ => 0 := by
      filter_upwards [Iio_mem_nhds h1] with v hv
      rw [(hlow v hv).deriv_eq]
      simp
    exact continuousAt_const.congr this.symm
  · push Not at h1
    rcases lt_trichotomy u ρ with h2 | h2 | h2
    · have hu : ρ / 2 < u := by linarith
      have hev : deriv (slopePowBump ρ p q) =ᶠ[nhds u] fun v =>
          ((q : ℝ) * deriv p v ^ (q - 1) * deriv (deriv p) v - deriv p v ^ (q + 1)) * Real.exp (-p v) := by
        filter_upwards [Ioo_mem_nhds hu h2] with v hv
        exact (slopePowBump_hasDerivAt hp hρ q hv.1 hv.2).deriv
      refine ContinuousAt.congr ?_ hev.symm
      have hu0 : 0 < u := by linarith
      have c1 : ContinuousAt (deriv p) u := (hasDerivAt_deriv_of_isCutoff hp hu0 h2).continuousAt
      have c2 : ContinuousAt (deriv (deriv p)) u := by
        have h3 := (iteratedDeriv_contDiffOn hp 2).contDiffAt (Ioo_mem_nhds hu0 h2)
        have e2 : iteratedDeriv 2 p = deriv (deriv p) := by
          rw [iteratedDeriv_succ, iteratedDeriv_one]
        rw [e2] at h3
        exact h3.continuousAt
      have c3 : ContinuousAt p u := (hasDerivAt_of_isCutoff hp hu0 h2).continuousAt
      exact (((continuousAt_const.mul (c1.pow _)).mul c2).sub (c1.pow _)).mul (c3.neg.rexp)
    · subst h2
      rw [ContinuousAt, hatρ.deriv]
      rw [Metric.tendsto_nhds]
      intro c hc
      have hball : Metric.ball u (min (u / 2) (c / (B + 1))) ∈ nhds u := Metric.ball_mem_nhds _ (by positivity)
      filter_upwards [hball] with x hx
      have h1' : |x - u| < min (u / 2) (c / (B + 1)) := by simpa [Real.dist_eq] using hx
      have h2' : |x - u| < u / 2 := lt_of_lt_of_le h1' (min_le_left _ _)
      have h3 : |x - u| < c / (B + 1) := lt_of_lt_of_le h1' (min_le_right _ _)
      rw [lt_div_iff₀ (by positivity)] at h3
      rw [Real.dist_eq, sub_zero]
      rcases lt_trichotomy x u with h4 | h4 | h4
      · have hx1 : u / 2 < x := by rw [abs_lt] at h2'; linarith
        rw [(slopePowBump_hasDerivAt hp hρ q hx1 h4).deriv]
        have h5 := (hB x hx1 h4).2
        have h6 : u - x = |x - u| := by rw [abs_of_neg (by linarith)]; ring
        rw [h6] at h5
        have h7 := abs_nonneg (x - u)
        nlinarith
      · rw [h4, hatρ.deriv, abs_zero]; exact hc
      · rw [(hhigh x h4).deriv_eq]
        simpa using hc
    · have : deriv (slopePowBump ρ p q) =ᶠ[nhds u] fun _ => 0 := by
        filter_upwards [Ioi_mem_nhds h2] with v hv
        rw [(hhigh v hv).deriv_eq]
        simp
      exact continuousAt_const.congr this.symm
private theorem contDiff_comp_norm {g : ℝ → ℝ} (hg : ContDiff ℝ 1 g) {c : ℝ} (hc : 0 < c)
    (h0 : ∀ u, |u| < c → g u = g 0) : ContDiff ℝ 1 (fun v : BondVector => g ‖v‖) := by
  rw [contDiff_iff_contDiffAt]
  intro v
  by_cases hv : v = 0
  · subst hv
    have hev : (fun v : BondVector => g ‖v‖) =ᶠ[nhds 0] fun _ => g 0 := by
      filter_upwards [Metric.ball_mem_nhds (0 : BondVector) hc] with w hw
      apply h0
      simpa using hw
    exact contDiffAt_const.congr_of_eventuallyEq hev
  · exact hg.contDiffAt.comp v (contDiffAt_norm ℝ hv)
section RadialField
private def radialField (ρ : ℝ) (v : BondVector) : BondVector :=
  Real.smoothTransition (2 - ‖v‖ ^ 2 / ρ ^ 2) • v
private theorem radialField_contDiff (ρ : ℝ) : ContDiff ℝ 1 (radialField ρ) := by
  unfold radialField
  have h1 : ContDiff ℝ 1 (fun v : BondVector => Real.smoothTransition (2 - ‖v‖ ^ 2 / ρ ^ 2)) :=
    (Real.smoothTransition.contDiff (n := 1)).comp (contDiff_const.sub ((contDiff_norm_sq ℝ).div_const _))
  exact h1.smul contDiff_id
private theorem radialField_eventuallyEq_id (hρ : 0 < ρ) {v : BondVector} (hv : ‖v‖ < ρ) :
    radialField ρ =ᶠ[nhds v] id := by
  filter_upwards [Metric.ball_mem_nhds v (sub_pos.2 hv)] with w hw
  have h1 : ‖w‖ < ρ := by
    have := norm_sub_norm_le w v
    have h2 : ‖w - v‖ < ρ - ‖v‖ := by simpa [dist_eq_norm] using hw
    linarith
  have h2 : ‖w‖ ^ 2 / ρ ^ 2 ≤ 1 := by
    rw [div_le_one (by positivity)]
    exact pow_le_pow_left₀ (norm_nonneg _) h1.le 2
  unfold radialField
  rw [Real.smoothTransition.one_of_one_le (by linarith)]
  simp
private theorem radialField_eq (hρ : 0 < ρ) {v : BondVector} (hv : ‖v‖ < ρ) : radialField ρ v = v :=
  (radialField_eventuallyEq_id hρ hv).eq_of_nhds
private theorem radialField_hasCompactSupport (hρ : 0 < ρ) : HasCompactSupport (radialField ρ) := by
  refine HasCompactSupport.intro (isCompact_closedBall (0 : BondVector) (2 * ρ)) fun v hv => ?_
  have h1 : 2 * ρ < ‖v‖ := by simpa using hv
  have h2 : 1 ≤ ‖v‖ ^ 2 / ρ ^ 2 * (1 / 4) := by
    have : (2 * ρ) ^ 2 ≤ ‖v‖ ^ 2 := pow_le_pow_left₀ (by positivity) h1.le 2
    rw [div_mul_div_comm, mul_one, le_div_iff₀ (by positivity)]
    nlinarith
  unfold radialField
  rw [Real.smoothTransition.zero_of_nonpos (by nlinarith), zero_smul]
private theorem radialField_bounds (hρ : 0 < ρ) :
    ∃ C : ℝ, (∀ v, ‖radialField ρ v‖ ≤ C) ∧ ∀ v, ‖fderiv ℝ (radialField ρ) v‖ ≤ C := by
  obtain ⟨C₁, h1⟩ := (radialField_contDiff ρ).continuous.bounded_above_of_compact_support
    (radialField_hasCompactSupport hρ)
  obtain ⟨C₂, h2⟩ := ((radialField_contDiff ρ).continuous_fderiv one_ne_zero).bounded_above_of_compact_support
    ((radialField_hasCompactSupport hρ).fderiv (𝕜 := ℝ))
  exact ⟨max C₁ C₂, fun v => (h1 v).trans (le_max_left _ _), fun v => (h2 v).trans (le_max_right _ _)⟩
private theorem radialField_divergence (hρ : 0 < ρ) {v : BondVector} (hv : ‖v‖ < ρ) :
    bondDivergence (radialField ρ) v = 3 := by
  unfold bondDivergence
  have h1 : fderiv ℝ (radialField ρ) v = ContinuousLinearMap.id ℝ BondVector := by
    rw [(radialField_eventuallyEq_id hρ hv).fderiv_eq]
    exact fderiv_id
  rw [h1]
  simp
end RadialField
section Integrability
variable {ι : Type} [Fintype ι] [DecidableEq ι]
private theorem cutoffFactor_le_one (hL : normalizedBallLawIsProbabilityStatement) (hρ : 0 < ρ)
    (hp : IsCutoff ρ p) {u : ℝ} (hu : 0 ≤ u) : cutoffFactor ρ p u ≤ 1 := by
  have h := (hL Unit ρ p (fun _ => 0) hρ hp continuous_const).2.2.2.2.2.2.2.2.2.2 0 u le_rfl hu
  have h0 : cutoffFactor ρ p 0 = 1 := by
    rw [cutoffFactor_of_lt hρ, hp.vanish_small 0 le_rfl (by positivity)]
    simp
  rwa [h0] at h
private theorem cutoffFactor_nonneg {u : ℝ} : 0 ≤ cutoffFactor ρ p u := by apply _root_.YangMills.Construction.CoarseFactorLocality.cutoffFactor_nonneg <;> assumption
private theorem integrable_radial_mul_density (hL : normalizedBallLawIsProbabilityStatement) (hρ : 0 < ρ)
    (hp : IsCutoff ρ p) {Ψ : BondField ι → ℝ} (hΨ : Continuous Ψ) {φ : ℝ → ℝ} {ψ : BondField ι → ℝ} {C : ℝ}
    (hφ : ContinuousOn φ (Set.Iio ρ)) (hb : ∀ u, 0 ≤ u → u < ρ → |φ u| * cutoffFactor ρ p u ≤ C)
    (hψ : Continuous ψ) (b : ι) :
    Integrable fun η => φ ‖η b‖ * ψ η * ballDensity (cutoffFactor ρ p) Ψ η := by
  obtain ⟨-, -, -, -, hmeas, hnn, hint, hpos, hcont, hne, hmono⟩ := hL ι ρ p Ψ hρ hp hΨ
  set B : Set (BondField ι) := {η | ∀ b, ‖η b‖ < ρ} with hB
  have hBball : B = Metric.ball 0 ρ := by
    ext η
    simp [hB, Metric.mem_ball, dist_zero_right, pi_norm_lt_iff hρ]
  have hBopen : IsOpen B := hBball ▸ Metric.isOpen_ball
  have hBfin : volume B ≠ ⊤ := by
    rw [hBball]
    exact (measure_ball_lt_top).ne
  set f : BondField ι → ℝ := fun η => φ ‖η b‖ * ψ η * ballDensity (cutoffFactor ρ p) Ψ η with hf
  have hzero : ∀ η, η ∉ B → f η = 0 := by
    intro η hη
    have : ballDensity (cutoffFactor ρ p) Ψ η = 0 := by
      by_contra h
      exact hη ((hne η).1 h)
    simp [hf, this]
  have hfc : ContinuousOn f B := by
    refine ContinuousOn.mul (ContinuousOn.mul ?_ hψ.continuousOn) hcont
    refine hφ.comp (continuous_norm.comp (continuous_apply b)).continuousOn fun η hη => ?_
    exact hη b
  obtain ⟨M, hM⟩ := (isCompact_closedBall (0 : BondField ι) ρ).exists_bound_of_continuousOn
    (f := fun η => ψ η * Real.exp (-Ψ η)) (hψ.mul (hΨ.neg.rexp)).continuousOn
  have hbound : ∀ η ∈ B, ‖f η‖ ≤ C * max M 0 := by
    intro η hη
    have hη' : ‖η‖ ≤ ρ := by
      have : η ∈ Metric.ball (0 : BondField ι) ρ := hBball ▸ hη
      exact (mem_ball_zero_iff.1 this).le
    have h1 := hM η (by simpa using hη')
    have hprod : ∏ c ∈ Finset.univ.erase b, cutoffFactor ρ p ‖η c‖ ≤ 1 :=
      Finset.prod_le_one (fun c _ => cutoffFactor_nonneg)
        (fun c _ => cutoffFactor_le_one hL hρ hp (norm_nonneg _))
    have hprod0 : 0 ≤ ∏ c ∈ Finset.univ.erase b, cutoffFactor ρ p ‖η c‖ :=
      Finset.prod_nonneg fun c _ => cutoffFactor_nonneg
    have e1 : f η = (φ ‖η b‖ * cutoffFactor ρ p ‖η b‖) * (∏ c ∈ Finset.univ.erase b, cutoffFactor ρ p ‖η c‖) *
        (ψ η * Real.exp (-Ψ η)) := by
      simp only [hf, ballDensity, radialWeightProd]
      rw [← Finset.mul_prod_erase Finset.univ _ (Finset.mem_univ b)]
      ring
    have h2 : |φ ‖η b‖ * cutoffFactor ρ p ‖η b‖| ≤ C := by
      rw [abs_mul, abs_of_nonneg (cutoffFactor_nonneg (p := p) (ρ := ρ) (u := ‖η b‖))]
      exact hb _ (norm_nonneg _) (hη b)
    have hC0 : 0 ≤ C := (abs_nonneg _).trans h2
    rw [e1, Real.norm_eq_abs, abs_mul, abs_mul, abs_of_nonneg hprod0]
    have h3 : |ψ η * Real.exp (-Ψ η)| ≤ max M 0 := by
      rw [← Real.norm_eq_abs]
      exact h1.trans (le_max_left _ _)
    calc _ ≤ C * 1 * max M 0 := by gcongr
      _ = _ := by ring
  have hOn : IntegrableOn f B := by
    have hsupp : Function.support f ⊆ B := fun η hη => by
      by_contra h
      exact hη (hzero η h)
    have hms : AEStronglyMeasurable f volume := by
      have h0 : AEStronglyMeasurable f (volume.restrict B) := hfc.aestronglyMeasurable hBopen.measurableSet
      have h := (aestronglyMeasurable_indicator_iff (μ := volume) hBopen.measurableSet).2 h0
      rwa [Set.indicator_eq_self.2 hsupp] at h
    refine Measure.integrableOn_of_bounded (M := C * max M 0) hBfin hms ?_
    filter_upwards [ae_restrict_mem hBopen.measurableSet] with η hη
    exact hbound η hη
  exact (integrableOn_iff_integrable_of_support_subset (fun η hη => by
    by_contra h
    exact hη (hzero η h))).1 hOn
end Integrability
private theorem mul_pow_le_young {q : ℕ} {c δ f : ℝ} (hc : 0 ≤ c) (hδ : 0 < δ) (hf : 0 ≤ f) :
    c * f ^ q ≤ δ * f ^ (q + 1) + c ^ (q + 1) * (1 / δ) ^ q := by
  by_cases h : c ≤ δ * f
  · have h1 : c * f ^ q ≤ δ * f * f ^ q := by gcongr
    have h2 : 0 ≤ c ^ (q + 1) * (1 / δ) ^ q := by positivity
    have h3 : δ * f * f ^ q = δ * f ^ (q + 1) := by ring
    linarith
  · push Not at h
    have h1 : f ≤ c * (1 / δ) := by
      rw [mul_one_div, le_div_iff₀ hδ]
      linarith
    have h2 : f ^ q ≤ (c * (1 / δ)) ^ q := pow_le_pow_left₀ hf h1 q
    have h3 : c * f ^ q ≤ c * (c * (1 / δ)) ^ q := by gcongr
    have h4 : c * (c * (1 / δ)) ^ q = c ^ (q + 1) * (1 / δ) ^ q := by rw [mul_pow]; ring
    have h5 : 0 ≤ δ * f ^ (q + 1) := by positivity
    linarith
private theorem slope_moment_pointwise {q : ℕ} (hq : 1 ≤ q) {ρ f u P2 A a₀ Cε : ℝ} (hρ : 0 < ρ) (hf : 0 ≤ f)
    (hu0 : 0 ≤ u) (hu : u ≤ ρ) (hsup : f ≠ 0 → 5 * ρ / 8 ≤ u) (hP2 : P2 ≤ 1 / (8 * (q : ℝ)) * f ^ 2 + Cε)
    (hA : |A| ≤ a₀) (hCε : 0 ≤ Cε) :
    ρ / 4 * f ^ (q + 1) ≤ f ^ q * (A + f * u - 3) - (q : ℝ) * f ^ (q - 1) * P2 * u +
      ((a₀ + 3 + (q : ℝ) * ρ * Cε) ^ (q + 1) * (1 / (ρ / 4)) ^ q + (q : ℝ) * ρ * Cε) := by
  obtain ⟨i, rfl⟩ : ∃ i, q = i + 1 := ⟨q - 1, by omega⟩
  simp only [Nat.add_sub_cancel]
  set b₀ := ((i + 1 : ℕ) : ℝ) * ρ * Cε with hb₀
  have ha₀ : 0 ≤ a₀ := (abs_nonneg _).trans hA
  have h1 : 5 * ρ / 8 * f ^ (i + 1 + 1) ≤ f ^ (i + 1 + 1) * u := by
    by_cases h0 : f = 0
    · simp [h0]
    · have := hsup h0
      rw [mul_comm]
      gcongr
  have h2 : f ^ (i + 1) * A ≥ -(a₀ * f ^ (i + 1)) := by
    have h3 := neg_abs_le A
    have h4 : 0 ≤ f ^ (i + 1) := by positivity
    nlinarith
  have h5 : ((i + 1 : ℕ) : ℝ) * f ^ i * P2 * u ≤ ρ / 8 * f ^ (i + 1 + 1) + b₀ * f ^ i := by
    have e1 : ((i + 1 : ℕ) : ℝ) * f ^ i * P2 ≤ ((i + 1 : ℕ) : ℝ) * f ^ i *
        (1 / (8 * ((i + 1 : ℕ) : ℝ)) * f ^ 2 + Cε) := by gcongr
    have e2 : ((i + 1 : ℕ) : ℝ) * f ^ i * (1 / (8 * ((i + 1 : ℕ) : ℝ)) * f ^ 2 + Cε) =
        1 / 8 * f ^ (i + 1 + 1) + ((i + 1 : ℕ) : ℝ) * Cε * f ^ i := by
      field_simp
      ring
    calc ((i + 1 : ℕ) : ℝ) * f ^ i * P2 * u
        ≤ (1 / 8 * f ^ (i + 1 + 1) + ((i + 1 : ℕ) : ℝ) * Cε * f ^ i) * u := by
          rw [← e2]; gcongr
      _ ≤ (1 / 8 * f ^ (i + 1 + 1) + ((i + 1 : ℕ) : ℝ) * Cε * f ^ i) * ρ := by gcongr
      _ = _ := by rw [hb₀]; ring
  have h6 : f ^ i ≤ 1 + f ^ (i + 1) := by
    by_cases h0 : f ≤ 1
    · have : f ^ i ≤ 1 := pow_le_one₀ hf h0
      have h7 : 0 ≤ f ^ (i + 1) := by positivity
      linarith
    · push Not at h0
      have : f ^ i ≤ f ^ (i + 1) := pow_le_pow_right₀ h0.le (by omega)
      linarith
  have hY := mul_pow_le_young (q := i + 1) (c := a₀ + 3 + b₀) (δ := ρ / 4) (f := f) (by positivity)
    (by positivity) hf
  have h7 : b₀ * f ^ i ≤ b₀ * (1 + f ^ (i + 1)) := by gcongr
  have e4 : f ^ (i + 1) * (A + f * u - 3) = f ^ (i + 1) * A + f ^ (i + 1 + 1) * u - 3 * f ^ (i + 1) := by ring
  rw [e4]
  nlinarith
private theorem norm_add_smul_self (v : BondVector) {t : ℝ} (ht : -1 < t) : ‖v + t • v‖ = (1 + t) * ‖v‖ := by
  have : v + t • v = (1 + t) • v := by module
  rw [this, norm_smul, Real.norm_of_nonneg (by linarith)]
section Moments
variable {ι : Type} [Fintype ι] [DecidableEq ι]
private theorem bondPartialDeriv_radial {g : ℝ → ℝ} (b : ι) (η : BondField ι) (hg : DifferentiableAt ℝ g ‖η b‖)
    (hd : DifferentiableAt ℝ (fun ζ : BondField ι => g ‖ζ b‖) η) :
    bondPartialDeriv (fun ζ : BondField ι => g ‖ζ b‖) b η (η b) = deriv g ‖η b‖ * ‖η b‖ := by
  by_cases hv : η b = 0
  · simp [bondPartialDeriv, bondVariation, hv]
  · have hu : 0 < ‖η b‖ := norm_pos_iff.2 hv
    have hline : HasDerivAt (fun t : ℝ => η + t • bondVariation b (η b)) (bondVariation b (η b)) 0 := by
      simpa using ((hasDerivAt_id (0 : ℝ)).smul_const (bondVariation b (η b))).const_add η
    have hd0 : HasFDerivAt (fun ζ : BondField ι => g ‖ζ b‖)
        (fderiv ℝ (fun ζ : BondField ι => g ‖ζ b‖) η) (η + (0 : ℝ) • bondVariation b (η b)) := by
      simpa using hd.hasFDerivAt
    have h1 := hd0.comp_hasDerivAt (0 : ℝ) hline
    have hinner : HasDerivAt (fun t : ℝ => (1 + t) * ‖η b‖) ‖η b‖ 0 := by
      have := ((hasDerivAt_id (0 : ℝ)).const_add 1).mul_const ‖η b‖
      simpa using this
    have hg0 : HasDerivAt g (deriv g ‖η b‖) ((1 + (0 : ℝ)) * ‖η b‖) := by
      simpa using hg.hasDerivAt
    have h2 := hg0.comp (0 : ℝ) hinner
    have hev : ((fun ζ : BondField ι => g ‖ζ b‖) ∘ fun t : ℝ => η + t • bondVariation b (η b)) =ᶠ[nhds 0]
        (g ∘ fun t : ℝ => (1 + t) * ‖η b‖) := by
      filter_upwards [Ioi_mem_nhds (show (-1 : ℝ) < 0 by norm_num)] with t ht
      have e : (η + t • bondVariation b (η b)) b = η b + t • η b := by simp [bondVariation]
      simp only [Function.comp, e, norm_add_smul_self _ ht]
    exact (h1.congr_of_eventuallyEq hev.symm).unique h2
private theorem clampedSlope_pow_mul_cutoff_le (hC : cutoffDerivBoundsStatement) (hρ : 0 < ρ) (hp : IsCutoff ρ p)
    (k : ℕ) : ∃ C : ℝ, 0 ≤ C ∧ ∀ u, 0 ≤ u → u < ρ → |clampedSlope ρ p u ^ k| * cutoffFactor ρ p u ≤ C := by
  obtain ⟨hnn, -, hpow, -⟩ := hC ρ p hρ hp
  obtain ⟨C, hC0, h⟩ := hpow k
  refine ⟨max C 1, le_trans zero_le_one (le_max_right _ _), fun u h0 h1 => ?_⟩
  rw [cutoffFactor_of_lt h1, abs_of_nonneg (pow_nonneg (clampedSlope_nonneg hC hρ hp h1) k)]
  by_cases hu : u ≤ ρ / 2
  · have hp0 : p u = 0 := hp.vanish_small u h0 (by linarith)
    rw [hp0]
    unfold clampedSlope
    rw [if_pos hu]
    by_cases hk : k = 0
    · subst hk; simp
    · rw [zero_pow hk]; simp
  · push Not at hu
    have hu0 : 0 < u := by linarith
    have hP := hnn u hu0 h1
    rw [clampedSlope_eq_deriv hu]
    refine le_trans ?_ (le_max_left _ _)
    refine le_trans ?_ (h u hu0 h1)
    have := Real.exp_pos (-p u)
    gcongr
    linarith
private theorem derivTerm_mul_cutoff_le (hC : cutoffDerivBoundsStatement) (hρ : 0 < ρ) (hp : IsCutoff ρ p) (q : ℕ) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ u, 5 * ρ / 8 ≤ u → u < ρ →
      |(q : ℝ) * deriv p u ^ (q - 1) * deriv (deriv p) u * u| * cutoffFactor ρ p u ≤ C := by
  obtain ⟨hnn, -, hpow, -, hder, -⟩ := hC ρ p hρ hp
  obtain ⟨C₂, k₂, hC₂, h2⟩ := hder 2 (by norm_num)
  obtain ⟨C₃, hC₃, h3⟩ := hpow (q - 1 + k₂)
  refine ⟨(q : ℝ) * C₂ * C₃ * ρ, by positivity, fun u hu1 hu2 => ?_⟩
  have hu0 : 0 < u := by linarith
  have hP := hnn u hu0 hu2
  have e2 : iteratedDeriv 2 p = deriv (deriv p) := by
    rw [iteratedDeriv_succ, iteratedDeriv_one]
  have h4 := h2 u hu0 hu2
  rw [e2] at h4
  have h5 := h3 u hu0 hu2
  rw [cutoffFactor_of_lt hu2]
  set P := deriv p u
  set e := Real.exp (-p u)
  have he0 : 0 < e := Real.exp_pos _
  rw [abs_mul, abs_mul, abs_mul, abs_of_nonneg (by positivity : (0 : ℝ) ≤ q),
    abs_of_nonneg (by positivity : 0 ≤ P ^ (q - 1)), abs_of_pos hu0]
  have h6 : P ^ (q - 1) ≤ (1 + P) ^ (q - 1) := pow_le_pow_left₀ hP (by linarith) _
  calc (q : ℝ) * P ^ (q - 1) * |deriv (deriv p) u| * u * e
      ≤ (q : ℝ) * (1 + P) ^ (q - 1) * (C₂ * (1 + P) ^ k₂) * ρ * e := by gcongr
    _ = (q : ℝ) * C₂ * ((1 + P) ^ (q - 1 + k₂) * e) * ρ := by rw [pow_add]; ring
    _ ≤ (q : ℝ) * C₂ * C₃ * ρ := by gcongr
private theorem clampedSlope_moment_le (hC : cutoffDerivBoundsStatement) (hMn : integralAlongFieldStatement)
    (hL : normalizedBallLawIsProbabilityStatement) (hR : CutoffFactorIsRadialCutoff) (hρ : 0 < ρ)
    (hp : IsCutoff ρ p) {Cx : ℝ} (hCx : 0 ≤ Cx) {q : ℕ} (hq : 1 ≤ q) :
    ∃ D : ℝ, 0 ≤ D ∧ ∀ (ι : Type) [Fintype ι] [DecidableEq ι] (x : ℝ) (Ψ : BondField ι → ℝ), 1 ≤ x →
      ContDiff ℝ 3 Ψ →
      (∀ η : BondField ι, (∀ b, ‖η b‖ < ρ) → ∀ (b : ι) (e : BondVector),
        |bondPartialDeriv Ψ b η e| ≤ Cx * x * ‖e‖) →
      ∀ b : ι, (∫ η, clampedSlope ρ p ‖η b‖ ^ (q + 1) * ballDensity (cutoffFactor ρ p) Ψ η) ≤
        D * x ^ (q + 1) * ∫ η, ballDensity (cutoffFactor ρ p) Ψ η := by
  obtain ⟨hnn, hzero, hpow, hp2, hder, -⟩ := hC ρ p hρ hp
  obtain ⟨Cε, hCε0, hε⟩ := hp2 (1 / (8 * (q : ℝ))) (by positivity)
  set b₀ : ℝ := (q : ℝ) * ρ * Cε with hb₀
  have hb₀0 : 0 ≤ b₀ := by positivity
  set A₁ : ℝ := Cx * ρ + 3 + b₀ with hA₁
  set E₀ : ℝ := A₁ ^ (q + 1) * (1 / (ρ / 4)) ^ q + b₀ with hE₀
  refine ⟨4 / ρ * E₀, by positivity, ?_⟩
  intro ι _ _ x Ψ hx hΨ hsl b
  have hΨc : Continuous Ψ := hΨ.continuous
  obtain ⟨-, -, -, -, hmeas, hdnn, hint, hZ, hcont, hne, hmono⟩ := hL ι ρ p Ψ hρ hp hΨc
  set dens := ballDensity (cutoffFactor ρ p) Ψ with hdens
  set g : ℝ → ℝ := fun u => clampedSlope ρ p u ^ q with hg
  set G : BondField ι → ℝ := fun η => g ‖η b‖ with hG
  have hq0 : q ≠ 0 := by omega
  have hg0 : ∀ u, u < 5 * ρ / 8 → g u = 0 := fun u hu => by
    simp only [hg]
    rw [clampedSlope_eq_zero hC hρ hp hu, zero_pow hq0]
  have hgs : ∀ u, u < ρ → ContDiffAt ℝ ∞ g u := fun u hu => (clampedSlope_contDiffAt hC hρ hp hu).pow q
  have hgd : ∀ u, u < ρ → DifferentiableAt ℝ g u := fun u hu =>
    (hgs u hu).differentiableAt (by simp)
  have hproj : ∀ c : ι, ContDiff ℝ 1 (fun η : BondField ι => η c) := fun c => contDiff_apply ℝ BondVector c
  have hGat : ∀ η : BondField ι, (∀ c, ‖η c‖ < ρ) → ContDiffAt ℝ 1 G η := by
    intro η hη
    by_cases hv : η b = 0
    · have hev : G =ᶠ[nhds η] fun _ => 0 := by
        have hopen : IsOpen {ζ : BondField ι | ‖ζ b‖ < 5 * ρ / 8} :=
          isOpen_lt (continuous_norm.comp (continuous_apply b)) continuous_const
        filter_upwards [hopen.mem_nhds (by simp [hv]; positivity)] with ζ hζ
        exact hg0 _ hζ
      exact contDiffAt_const.congr_of_eventuallyEq hev
    · have h1 : ContDiffAt ℝ 1 (fun ζ : BondField ι => ‖ζ b‖) η :=
        (contDiffAt_norm ℝ hv).comp η (hproj b).contDiffAt
      have h2 : ContDiffAt ℝ 1 g ‖η b‖ := (hgs _ (hη b)).of_le (by exact_mod_cast (le_top : (1 : ℕ∞) ≤ ⊤))
      exact ContDiffAt.comp (g := g) η h2 h1
  have hGon : ContDiffOn ℝ 1 G {η | ∀ b, ‖η b‖ < ρ} := fun η hη => (hGat η hη).contDiffWithinAt
  have hF : (fun η => G η * dens η) = fun η => slopePowBump ρ p q ‖η b‖ *
      (∏ c ∈ Finset.univ.erase b, cutoffFactor ρ p ‖η c‖) * Real.exp (-Ψ η) := by
    funext η
    simp only [hG, hg, hdens, ballDensity, radialWeightProd, slopePowBump]
    rw [← Finset.mul_prod_erase Finset.univ _ (Finset.mem_univ b)]
    ring
  have hRr := hR ρ p hρ hp
  have hcR : ContDiff ℝ 1 (fun v : BondVector => cutoffFactor ρ p ‖v‖) := by
    have hone : ∀ w : ℝ, 0 ≤ w → w ≤ 5 * ρ / 8 → cutoffFactor ρ p w = 1 := fun w h0 h1 => by
      have := hRr.one w h0 h1
      simpa [max_eq_left h0] using this
    have h1 := contDiff_comp_norm hRr.smooth (c := 5 * ρ / 8) (by positivity) (fun u hu => by
      have hu' := abs_lt.1 hu
      rw [hone (max u 0) (le_max_right _ _) (max_le hu'.2.le (by positivity)),
        hone (max 0 0) (le_max_right _ _) (by simp; positivity)])
    simpa [norm_nonneg] using h1
  have hcB : ContDiff ℝ 1 (fun v : BondVector => slopePowBump ρ p q ‖v‖) :=
    contDiff_comp_norm (slopePowBump_contDiff hC hp hρ hq) (c := 5 * ρ / 8) (by positivity) (fun u hu => by
      rw [slopePowBump_eq_zero_of_lt hC hρ hp hq (abs_lt.1 hu).2,
        slopePowBump_eq_zero_of_lt hC hρ hp hq (by positivity)])
  have hFs : ContDiff ℝ 1 (fun η => G η * dens η) := by
    rw [hF]
    exact ((hcB.comp (hproj b)).mul (contDiff_prod fun c _ => hcR.comp (hproj c))).mul
      ((hΨ.of_le (by norm_num)).neg.exp)
  have hoff : ∀ η, ¬ (∀ c, ‖η c‖ < ρ) → dens η = 0 := fun η hη => by
    by_contra h
    exact hη ((hne η).1 h)
  have hFnn : ∀ η, 0 ≤ G η * dens η := fun η => by
    by_cases hη : ∀ c, ‖η c‖ < ρ
    · exact mul_nonneg (pow_nonneg (clampedSlope_nonneg hC hρ hp (hη b)) q) (hdnn η)
    · rw [hoff η hη, mul_zero]
  have hvan : DensityProductVanishesAtBoundary ρ p Ψ G := ⟨hFs.differentiable (by norm_num), fun η hη => by
    have hmin : IsLocalMin (fun ζ => G ζ * dens ζ) η := Filter.Eventually.of_forall fun ζ => by
      simp only [hoff η hη, mul_zero]
      exact hFnn ζ
    exact hmin.fderiv_eq_zero⟩
  have hFc : HasCompactSupport (fun η => G η * dens η) := by
    refine HasCompactSupport.intro (isCompact_closedBall (0 : BondField ι) ρ) fun η hη => ?_
    have : ¬ (∀ c, ‖η c‖ < ρ) := fun h => hη (by
      simpa using (pi_norm_le_iff_of_nonneg hρ.le).2 fun c => (h c).le)
    simp [hoff η this]
  have hFint : Integrable (fun η => G η * dens η) := hFs.continuous.integrable_of_hasCompactSupport hFc
  have hFder : ∀ e : BondVector, Integrable fun η => fderiv ℝ (fun ζ => G ζ * dens ζ) η (bondVariation b e) :=
    fun e => ((hFs.continuous_fderiv one_ne_zero).clm_apply continuous_const).integrable_of_hasCompactSupport
      (hFc.fderiv_apply (𝕜 := ℝ) _)
  obtain ⟨Cz, hz1, hz2⟩ := radialField_bounds hρ
  have hAl : ∀ η : BondField ι, (∀ c, ‖η c‖ < ρ) →
      fieldDerivative b (radialField ρ) G η = deriv g ‖η b‖ * ‖η b‖ := fun η hη => by
    unfold fieldDerivative
    rw [radialField_eq hρ (hη b)]
    exact bondPartialDeriv_radial b η (hgd _ (hη b)) ((hGat η hη).differentiableAt (by norm_num))
  have hgz : ∀ u, u < 5 * ρ / 8 → deriv g u = 0 := fun u hu => by
    have hev : g =ᶠ[nhds u] fun _ => 0 := by
      filter_upwards [Iio_mem_nhds hu] with v hv
      exact hg0 v hv
    rw [hev.deriv_eq]
    simp
  have hgf : ∀ u, ρ / 2 < u → u < ρ → deriv g u = (q : ℝ) * deriv p u ^ (q - 1) * deriv (deriv p) u := by
    intro u h1 h2
    have hev : g =ᶠ[nhds u] fun v => deriv p v ^ q := by
      filter_upwards [Ioi_mem_nhds h1] with v hv
      simp only [hg]
      rw [clampedSlope_eq_deriv hv]
    rw [hev.deriv_eq]
    exact ((hasDerivAt_deriv_of_isCutoff hp (by linarith) h2).fun_pow q).deriv
  have hdc : ContinuousOn (deriv g) (Set.Iio ρ) := by
    have hgOn : ContDiffOn ℝ ∞ g (Set.Iio ρ) := fun u hu => (hgs u hu).contDiffWithinAt
    exact ((contDiffOn_infty_iff_deriv_of_isOpen isOpen_Iio).1 hgOn).2.continuousOn
  obtain ⟨C4, hC40, hC4⟩ := derivTerm_mul_cutoff_le hC hρ hp q
  have hAlongI : Integrable (fun η => fieldDerivative b (radialField ρ) G η * dens η) := by
    have h1 := integrable_radial_mul_density hL hρ hp hΨc (φ := fun u => deriv g u * u) (ψ := fun _ => 1)
      (C := C4) (hdc.mul continuousOn_id) (fun u h0 h1 => by
        by_cases hu : u < 5 * ρ / 8
        · simpa [hgz u hu] using hC40
        · push Not at hu
          rw [hgf u (by linarith) h1]
          exact hC4 u hu h1) continuous_const b
    refine h1.congr (Filter.Eventually.of_forall fun η => ?_)
    by_cases hη : ∀ c, ‖η c‖ < ρ
    · simp only [mul_one, hAl η hη]
      rfl
    · have h0 := hoff η hη
      show deriv g ‖η b‖ * ‖η b‖ * 1 * dens η = fieldDerivative b (radialField ρ) G η * dens η
      rw [h0, mul_zero, mul_zero]
  set A : BondField ι → ℝ := fun η => bondPartialDeriv Ψ b η (η b) with hA
  have hAc : Continuous A := by
    have h1 : Continuous fun η : BondField ι => bondVariation b (η b) := by
      unfold bondVariation
      exact continuous_const.update b (continuous_apply b)
    exact (hΨ.continuous_fderiv (by norm_num)).clm_apply h1
  have hSc : ∀ η : BondField ι, (∀ c, ‖η c‖ < ρ) → G η * fieldScore p Ψ b (radialField ρ) η =
      g ‖η b‖ * A η + clampedSlope ρ p ‖η b‖ ^ (q + 1) * ‖η b‖ - 3 * g ‖η b‖ := by
    intro η hη
    unfold fieldScore
    rw [radialField_eq hρ (hη b), radialField_divergence hρ (hη b)]
    by_cases hu : ‖η b‖ < 5 * ρ / 8
    · have h1 : G η = 0 := hg0 _ hu
      have h2 : g ‖η b‖ = 0 := hg0 _ hu
      rw [h1, h2, clampedSlope_eq_zero hC hρ hp hu]
      simp
    · push Not at hu
      have hu2 : ρ / 2 < ‖η b‖ := by linarith
      have hupos : ‖η b‖ ≠ 0 := by intro h; rw [h] at hu2; linarith
      have e1 : radialCutoffSlope p (η b) (η b) = deriv p ‖η b‖ * ‖η b‖ := by
        unfold radialCutoffSlope
        rw [real_inner_self_eq_norm_sq]
        field_simp
      simp only [hG, hg]
      rw [e1, clampedSlope_eq_deriv hu2, hA]
      simp only
      ring
  obtain ⟨Cg, hCg0, hCg⟩ := clampedSlope_pow_mul_cutoff_le hC hρ hp q
  obtain ⟨Cg1, hCg10, hCg1⟩ := clampedSlope_pow_mul_cutoff_le hC hρ hp (q + 1)
  have hsc : ∀ k : ℕ, ContinuousOn (fun u => clampedSlope ρ p u ^ k) (Set.Iio ρ) := fun k u hu =>
    ((clampedSlope_contDiffAt hC hρ hp hu).pow k).continuousAt.continuousWithinAt
  have hgI : Integrable (fun η => g ‖η b‖ * (1 : ℝ) * dens η) :=
    integrable_radial_mul_density hL hρ hp hΨc (hsc q) hCg continuous_const b
  have hgAI : Integrable (fun η => g ‖η b‖ * A η * dens η) :=
    integrable_radial_mul_density hL hρ hp hΨc (hsc q) hCg hAc b
  have hg1I : Integrable (fun η => clampedSlope ρ p ‖η b‖ ^ (q + 1) * (1 : ℝ) * dens η) :=
    integrable_radial_mul_density hL hρ hp hΨc (hsc (q + 1)) hCg1 continuous_const b
  have hg2I : Integrable (fun η => (clampedSlope ρ p ‖η b‖ ^ (q + 1) * ‖η b‖) * (1 : ℝ) * dens η) :=
    integrable_radial_mul_density hL hρ hp hΨc (φ := fun u => clampedSlope ρ p u ^ (q + 1) * u) (C := Cg1 * ρ)
      ((hsc (q + 1)).mul continuousOn_id) (fun u h0 h1 => by
        have h2 := hCg1 u h0 h1
        rw [abs_mul, abs_of_nonneg h0]
        have h3 : 0 ≤ |clampedSlope ρ p u ^ (q + 1)| * cutoffFactor ρ p u :=
          mul_nonneg (abs_nonneg _) cutoffFactor_nonneg
        calc |clampedSlope ρ p u ^ (q + 1)| * u * cutoffFactor ρ p u
            = (|clampedSlope ρ p u ^ (q + 1)| * cutoffFactor ρ p u) * u := by ring
          _ ≤ Cg1 * ρ := by gcongr) continuous_const b
  have hScoreI : Integrable (fun η => G η * fieldScore p Ψ b (radialField ρ) η * dens η) := by
    have h1 := (hgAI.add hg2I).sub (hgI.const_mul 3)
    refine h1.congr (Filter.Eventually.of_forall fun η => ?_)
    by_cases hη : ∀ c, ‖η c‖ < ρ
    · simp only [Pi.add_apply, Pi.sub_apply, hSc η hη]
      ring
    · simp only [Pi.add_apply, Pi.sub_apply, hoff η hη, mul_zero, sub_zero, add_zero]
  have hMean := hMn ι ρ p Ψ G b (radialField ρ) Cz hρ hp ((hΨ.of_le (by norm_num)).contDiffOn) hGon
    (radialField_contDiff ρ) hz1 hz2 hvan hFint hFder hAlongI hScoreI
  set a₀ : ℝ := Cx * x * ρ with ha₀
  set E : ℝ := (a₀ + 3 + b₀) ^ (q + 1) * (1 / (ρ / 4)) ^ q + b₀ with hE
  have hpt : ∀ η, ρ / 4 * (clampedSlope ρ p ‖η b‖ ^ (q + 1) * (1 : ℝ) * dens η) ≤
      (G η * fieldScore p Ψ b (radialField ρ) η * dens η - fieldDerivative b (radialField ρ) G η * dens η) +
        E * dens η := by
    intro η
    by_cases hη : ∀ c, ‖η c‖ < ρ
    · have hd := hdnn η
      have hun : 0 ≤ ‖η b‖ := norm_nonneg _
      by_cases hu : ‖η b‖ < 5 * ρ / 8
      · have h1 : G η * fieldScore p Ψ b (radialField ρ) η = 0 := by
          have : G η = 0 := hg0 _ hu
          rw [this, zero_mul]
        rw [h1, hAl η hη, hgz _ hu, clampedSlope_eq_zero hC hρ hp hu, zero_pow (by omega)]
        simp only [zero_mul, mul_zero, sub_zero, zero_add]
        positivity
      · push Not at hu
        have hu2 : ρ / 2 < ‖η b‖ := by linarith
        have hu0 : 0 < ‖η b‖ := by linarith
        have hP := hnn _ hu0 (hη b)
        have hAb : |A η| ≤ a₀ := by
          have h1 := hsl η hη b (η b)
          have h2 : 0 ≤ Cx * x := by positivity
          refine h1.trans ?_
          rw [ha₀]
          gcongr
          exact (hη b).le
        have hstep := slope_moment_pointwise hq hρ (f := deriv p ‖η b‖) (u := ‖η b‖)
          (P2 := deriv (deriv p) ‖η b‖) (A := A η) (a₀ := a₀) (Cε := Cε) hP hun (hη b).le (fun _ => hu)
          (hε _ hu0 (hη b)) hAb hCε0
        rw [← hb₀, ← hE] at hstep
        have h3 := mul_le_mul_of_nonneg_right hstep hd
        have e1 : G η * fieldScore p Ψ b (radialField ρ) η =
            deriv p ‖η b‖ ^ q * (A η + deriv p ‖η b‖ * ‖η b‖ - 3) := by
          rw [hSc η hη]
          simp only [hg]
          rw [clampedSlope_eq_deriv hu2]
          ring
        rw [e1, hAl η hη, hgf _ hu2 (hη b), clampedSlope_eq_deriv hu2]
        calc _ = ρ / 4 * deriv p ‖η b‖ ^ (q + 1) * dens η := by ring
          _ ≤ _ := h3
          _ = _ := by ring
    · simp [hoff η hη]
  have hi1 := hg1I.const_mul (ρ / 4)
  have hi2 := (hScoreI.sub hAlongI).add (hint.const_mul E)
  have hmono' := integral_mono hi1 hi2 hpt
  have hMean' : (∫ η, fieldDerivative b (radialField ρ) G η * dens η) =
      ∫ η, G η * fieldScore p Ψ b (radialField ρ) η * dens η := hMean
  rw [integral_const_mul, integral_add' (hScoreI.sub hAlongI) (hint.const_mul E),
    integral_sub' hScoreI hAlongI, integral_const_mul, ← hMean', sub_self, zero_add] at hmono'
  have hI1 : (∫ η, clampedSlope ρ p ‖η b‖ ^ (q + 1) * (1 : ℝ) * dens η) =
      ∫ η, clampedSlope ρ p ‖η b‖ ^ (q + 1) * dens η := by
    congr 1
    funext η
    ring
  rw [hI1] at hmono'
  have hEE : E ≤ E₀ * x ^ (q + 1) := by
    have h1 : a₀ + 3 + b₀ ≤ A₁ * x := by
      have h2 : 3 + b₀ ≤ (3 + b₀) * x := by nlinarith
      rw [hA₁, ha₀]
      nlinarith
    have h3 : (a₀ + 3 + b₀) ^ (q + 1) ≤ (A₁ * x) ^ (q + 1) := pow_le_pow_left₀ (by positivity) h1 _
    have h4 : (1 : ℝ) ≤ x ^ (q + 1) := one_le_pow₀ hx
    rw [hE, hE₀, add_mul]
    have h6 : b₀ ≤ b₀ * x ^ (q + 1) := by nlinarith
    have h7 : (a₀ + 3 + b₀) ^ (q + 1) * (1 / (ρ / 4)) ^ q ≤ A₁ ^ (q + 1) * (1 / (ρ / 4)) ^ q * x ^ (q + 1) := by
      calc _ ≤ (A₁ * x) ^ (q + 1) * (1 / (ρ / 4)) ^ q := by gcongr
        _ = _ := by rw [mul_pow]; ring
    linarith
  have hfin : ρ / 4 * ∫ η, clampedSlope ρ p ‖η b‖ ^ (q + 1) * dens η ≤
      ρ / 4 * (4 / ρ * E₀ * x ^ (q + 1) * ∫ η, dens η) := by
    refine hmono'.trans ?_
    have e2 : ρ / 4 * (4 / ρ * E₀ * x ^ (q + 1) * ∫ η, dens η) = (E₀ * x ^ (q + 1)) * ∫ η, dens η := by
      field_simp
    rw [e2]
    gcongr
  exact le_of_mul_le_mul_left hfin (by positivity)
private theorem one_add_pow_le_two_pow_mul {S : ℝ} (hS : 0 ≤ S) (m : ℕ) : (1 + S) ^ m ≤ 2 ^ m * (1 + S ^ m) := by
  by_cases h : S ≤ 1
  · have h1 : (1 + S) ^ m ≤ 2 ^ m := pow_le_pow_left₀ (by linarith) (by linarith) m
    have h2 : 0 ≤ S ^ m := by positivity
    have h3 : (0 : ℝ) ≤ 2 ^ m := by positivity
    nlinarith
  · push Not at h
    have h1 : (1 + S) ^ m ≤ (2 * S) ^ m := pow_le_pow_left₀ (by linarith) (by linarith) m
    rw [mul_pow] at h1
    have h3 : (0 : ℝ) ≤ 2 ^ m := by positivity
    nlinarith
abbrev _root_.YangMills.SharedProofs.p7069 := @one_add_pow_le_two_pow_mul
private theorem mul_le_half_sq_add {a b t : ℝ} (ht : 0 < t) : a * b ≤ t / 2 * a ^ 2 + 1 / (2 * t) * b ^ 2 := by
  have h2 : t / 2 * a ^ 2 + 1 / (2 * t) * b ^ 2 - a * b = (t * a - b) ^ 2 / (2 * t) := by
    field_simp
    ring
  have h3 : 0 ≤ (t * a - b) ^ 2 / (2 * t) := by positivity
  linarith
private theorem ae_bond_ne_zero {ι : Type} [Fintype ι] [DecidableEq ι] (b : ι) :
    ∀ᵐ η : BondField ι, η b ≠ 0 := by
  set s : Submodule ℝ (BondField ι) := LinearMap.ker (LinearMap.proj b) with hs
  have hne : s ≠ ⊤ := by
    intro h
    have h1 : bondVariation b (EuclideanSpace.single (0 : Fin 3) (1 : ℝ)) ∈ s := by rw [h]; trivial
    have h2 : (bondVariation b (EuclideanSpace.single (0 : Fin 3) (1 : ℝ)) : BondField ι) b = 0 := by
      simpa [hs] using h1
    have h3 : (EuclideanSpace.single (0 : Fin 3) (1 : ℝ)) = 0 := by
      simpa [bondVariation] using h2
    have h4 := congrArg (fun v : BondVector => v 0) h3
    simp at h4
  have h0 := Measure.addHaar_submodule (volume : Measure (BondField ι)) s hne
  rw [ae_iff]
  refine measure_mono_null (fun η hη => ?_) h0
  simp only [ne_eq, not_not, Set.mem_ofPred_eq] at hη
  simpa [hs] using hη
theorem cutoffDerivMomentsStatement_holds (hC : cutoffDerivBoundsStatement) (hMn : integralAlongFieldStatement)
    (hL : normalizedBallLawIsProbabilityStatement) (hR : CutoffFactorIsRadialCutoff)
    (hMom : GaussianMomentBound) : cutoffDerivMomentsStatement := by
  intro ρ p lam C W hρ hp hlam hC0 hW0 j q N hj hq
  obtain ⟨hnn, hzero, hpow, -, hder, -⟩ := hC ρ p hρ hp
  obtain ⟨C₁, k, hC₁, hd⟩ := hder j hj
  obtain ⟨Ck, hCk0, hCk⟩ := hpow (k * q)
  set Q : ℕ := k * q + 1 with hQ
  set n : ℕ := Q + N with hn
  obtain ⟨D, hD0, hD⟩ := clampedSlope_moment_le hC hMn hL hR hρ hp hC0 (q := 2 * Q - 1) (by omega)
  have h2Q : 2 * Q - 1 + 1 = 2 * Q := by omega
  rw [h2Q] at hD
  set Pn : ℝ := ∏ i ∈ Finset.range (2 * n), (4 * (i : ℝ) + 8 * W) with hPn
  have hPn0 : 0 ≤ Pn := Finset.prod_nonneg fun i _ => by positivity
  set Mn : ℝ := Pn * (4 / lam) ^ (2 * n) with hMn'
  have hMn0 : 0 ≤ Mn := by positivity
  set B₀ : ℝ := C₁ ^ q * (8 / (5 * ρ)) ^ (2 * n) with hB₀
  have hB₀0 : 0 ≤ B₀ := by positivity
  refine ⟨B₀ * (2 ^ (2 * Q) * (1 + D) / 2 + Mn / 2), by positivity, ?_⟩
  intro ι _ _ x κ d Ψ K hx hκ hdist hcv hWs hs0 hsl b
  have hΨ := hcv.smooth
  have hΨc : Continuous Ψ := hΨ.continuous
  obtain ⟨-, -, -, -, hmeas, hdnn, hint, hZ, hcont, hne, hmono⟩ := hL ι ρ p Ψ hρ hp hΨc
  set dens := ballDensity (cutoffFactor ρ p) Ψ with hdens
  have hoff : ∀ η, ¬ (∀ c, ‖η c‖ < ρ) → dens η = 0 := fun η hη => by
    by_contra h
    exact hη ((hne η).1 h)
  have hx0 : 0 < x := by linarith
  set φ : ℝ → ℝ := fun u => if u ≤ ρ / 2 then 0 else |iteratedDeriv j p u| ^ q with hφ
  have hq0 : q ≠ 0 := by omega
  have hφlow : ∀ u, u < 5 * ρ / 8 → φ u = 0 := fun u hu => by
    simp only [hφ]
    split_ifs with h
    · rfl
    · push Not at h
      rw [hzero u (by linarith) hu j hj, abs_zero, zero_pow hq0]
  have hφc : ContinuousOn φ (Set.Iio ρ) := by
    intro u hu
    by_cases h : u < 5 * ρ / 8
    · have hev : φ =ᶠ[nhds u] fun _ => 0 := by
        filter_upwards [Iio_mem_nhds h] with v hv
        exact hφlow v hv
      exact (continuousAt_const.congr hev.symm).continuousWithinAt
    · push Not at h
      have h1 : ρ / 2 < u := by linarith
      have hu' : u < ρ := hu
      have hev : φ =ᶠ[nhds u] fun v => |iteratedDeriv j p v| ^ q := by
        filter_upwards [Ioi_mem_nhds h1] with v hv
        simp only [hφ]
        rw [if_neg (not_le.2 hv)]
      have hc : ContinuousAt (iteratedDeriv j p) u :=
        ((iteratedDeriv_contDiffOn hp j).contDiffAt (Ioo_mem_nhds (by linarith) hu')).continuousAt
      exact ((hc.abs.pow q).congr hev.symm).continuousWithinAt
  have hφb : ∀ u, 0 ≤ u → u < ρ → |φ u| * cutoffFactor ρ p u ≤ C₁ ^ q * Ck := by
    intro u h0 h1
    by_cases h : u ≤ ρ / 2
    · rw [hφlow u (by linarith)]
      simp only [abs_zero, zero_mul]
      positivity
    · push Not at h
      have hu0 : 0 < u := by linarith
      have e : φ u = |iteratedDeriv j p u| ^ q := by
        simp only [hφ]
        rw [if_neg (not_le.2 h)]
      rw [e, abs_of_nonneg (by positivity), cutoffFactor_of_lt h1]
      have hP := hnn u hu0 h1
      have h2 := hd u hu0 h1
      have h3 := hCk u hu0 h1
      calc |iteratedDeriv j p u| ^ q * Real.exp (-p u)
          ≤ (C₁ * (1 + deriv p u) ^ k) ^ q * Real.exp (-p u) := by gcongr
        _ = C₁ ^ q * ((1 + deriv p u) ^ (k * q) * Real.exp (-p u)) := by rw [mul_pow, ← pow_mul]; ring
        _ ≤ C₁ ^ q * Ck := by gcongr
  have hφI := integrable_radial_mul_density hL hρ hp hΨc (ψ := fun _ => (1 : ℝ)) hφc hφb continuous_const b
  have hae : ∀ᵐ η : BondField ι, φ ‖η b‖ * (1 : ℝ) * dens η = |iteratedDeriv j p ‖η b‖| ^ q * dens η := by
    filter_upwards [ae_bond_ne_zero b] with η hη
    have hu0 : 0 < ‖η b‖ := norm_pos_iff.2 hη
    by_cases h : ‖η b‖ ≤ ρ / 2
    · rw [hφlow _ (by linarith), hzero _ hu0 (by linarith) j hj, abs_zero, zero_pow hq0]
      simp
    · simp only [hφ]
      rw [if_neg h, mul_one]
  refine ⟨hφI.congr hae, ?_⟩
  set t : ℝ := (x ^ (2 * Q + N))⁻¹ with ht
  have ht0 : 0 < t := by positivity
  obtain ⟨Cs2, hCs20, hCs2⟩ := clampedSlope_pow_mul_cutoff_le hC hρ hp (2 * Q)
  have hsc : ContinuousOn (fun u => clampedSlope ρ p u ^ (2 * Q)) (Set.Iio ρ) := fun u hu =>
    ((clampedSlope_contDiffAt hC hρ hp hu).pow (2 * Q)).continuousAt.continuousWithinAt
  have hSI := integrable_radial_mul_density hL hρ hp hΨc (ψ := fun _ => (1 : ℝ)) hsc hCs2 continuous_const b
  have hUI := integrable_radial_mul_density hL hρ hp hΨc (φ := fun u => u ^ (2 * (2 * n))) (ψ := fun _ => 1)
    (C := ρ ^ (2 * (2 * n))) (continuous_pow _).continuousOn (fun u h0 h1 => by
      rw [abs_of_nonneg (by positivity)]
      have h2 := cutoffFactor_le_one hL hρ hp h0
      have h3 : u ^ (2 * (2 * n)) ≤ ρ ^ (2 * (2 * n)) := pow_le_pow_left₀ h0 h1.le _
      have h4 : 0 ≤ u ^ (2 * (2 * n)) := by positivity
      have h5 : (0 : ℝ) ≤ cutoffFactor ρ p u := cutoffFactor_nonneg
      nlinarith) continuous_const b
  have hpt : ∀ᵐ η : BondField ι, |iteratedDeriv j p ‖η b‖| ^ q * dens η ≤
      B₀ * (t / 2 * 2 ^ (2 * Q) * (dens η + clampedSlope ρ p ‖η b‖ ^ (2 * Q) * (1 : ℝ) * dens η) +
        1 / (2 * t) * (‖η b‖ ^ (2 * (2 * n)) * (1 : ℝ) * dens η)) := by
    filter_upwards [ae_bond_ne_zero b] with η hη
    have hu0 : 0 < ‖η b‖ := norm_pos_iff.2 hη
    by_cases hball : ∀ c, ‖η c‖ < ρ
    · have hdd := hdnn η
      set u := ‖η b‖ with hu
      have huρ : u < ρ := hball b
      have hS0 : 0 ≤ clampedSlope ρ p u := clampedSlope_nonneg hC hρ hp huρ
      have hRnn : 0 ≤ t / 2 * 2 ^ (2 * Q) * (1 + clampedSlope ρ p u ^ (2 * Q)) +
          1 / (2 * t) * u ^ (2 * (2 * n)) := by positivity
      by_cases hlow : u < 5 * ρ / 8
      · rw [hzero u hu0 hlow j hj, abs_zero, zero_pow hq0, zero_mul]
        have : 0 ≤ B₀ * ((t / 2 * 2 ^ (2 * Q) * (1 + clampedSlope ρ p u ^ (2 * Q)) +
            1 / (2 * t) * u ^ (2 * (2 * n))) * dens η) := by positivity
        calc (0 : ℝ) ≤ _ := this
          _ = _ := by ring
      · push Not at hlow
        have hS : clampedSlope ρ p u = deriv p u := clampedSlope_eq_deriv (by linarith)
        have h1 : |iteratedDeriv j p u| ^ q ≤ C₁ ^ q * (1 + clampedSlope ρ p u) ^ (k * q) := by
          rw [hS]
          calc |iteratedDeriv j p u| ^ q ≤ (C₁ * (1 + deriv p u) ^ k) ^ q := by
                have := hd u hu0 huρ
                gcongr
            _ = _ := by rw [mul_pow, ← pow_mul]
        have hone : (1 : ℝ) ≤ 1 + clampedSlope ρ p u := by linarith
        have h2 : (1 + clampedSlope ρ p u) ^ (k * q) ≤ (1 + clampedSlope ρ p u) ^ Q :=
          pow_le_pow_right₀ hone (by omega)
        have h3 : 1 ≤ (8 / (5 * ρ) * u) ^ (2 * n) := by
          apply one_le_pow₀
          rw [div_mul_eq_mul_div, le_div_iff₀ (by positivity)]
          linarith
        have h4 := mul_le_half_sq_add (a := (1 + clampedSlope ρ p u) ^ Q) (b := u ^ (2 * n)) ht0
        have h5 := one_add_pow_le_two_pow_mul hS0 (2 * Q)
        have h6 : |iteratedDeriv j p u| ^ q ≤ B₀ * (t / 2 * 2 ^ (2 * Q) * (1 + clampedSlope ρ p u ^ (2 * Q)) +
            1 / (2 * t) * u ^ (2 * (2 * n))) := by
          have e1 : ((1 + clampedSlope ρ p u) ^ Q) ^ 2 = (1 + clampedSlope ρ p u) ^ (2 * Q) := by
            rw [← pow_mul, mul_comm]
          have e2 : (u ^ (2 * n)) ^ 2 = u ^ (2 * (2 * n)) := by
            rw [← pow_mul, mul_comm (2 * n) 2]
          rw [e1, e2] at h4
          have h7 : (1 + clampedSlope ρ p u) ^ Q * u ^ (2 * n) ≤
              t / 2 * (2 ^ (2 * Q) * (1 + clampedSlope ρ p u ^ (2 * Q))) + 1 / (2 * t) * u ^ (2 * (2 * n)) := by
            refine h4.trans ?_
            gcongr
          calc |iteratedDeriv j p u| ^ q ≤ C₁ ^ q * (1 + clampedSlope ρ p u) ^ Q * 1 := by
                rw [mul_one]
                refine h1.trans ?_
                gcongr
            _ ≤ C₁ ^ q * (1 + clampedSlope ρ p u) ^ Q * (8 / (5 * ρ) * u) ^ (2 * n) := by gcongr
            _ = B₀ * ((1 + clampedSlope ρ p u) ^ Q * u ^ (2 * n)) := by rw [hB₀, mul_pow]; ring
            _ ≤ B₀ * (t / 2 * (2 ^ (2 * Q) * (1 + clampedSlope ρ p u ^ (2 * Q))) +
                1 / (2 * t) * u ^ (2 * (2 * n))) := by gcongr
            _ = _ := by ring
        calc |iteratedDeriv j p u| ^ q * dens η
            ≤ B₀ * (t / 2 * 2 ^ (2 * Q) * (1 + clampedSlope ρ p u ^ (2 * Q)) +
                1 / (2 * t) * u ^ (2 * (2 * n))) * dens η := by gcongr
          _ = _ := by ring
    · simp [hoff η hball]
  have hRI : Integrable (fun η => B₀ * (t / 2 * 2 ^ (2 * Q) *
      (dens η + clampedSlope ρ p ‖η b‖ ^ (2 * Q) * (1 : ℝ) * dens η) +
      1 / (2 * t) * (‖η b‖ ^ (2 * (2 * n)) * (1 : ℝ) * dens η))) :=
    (((hint.add hSI).const_mul _).add (hUI.const_mul _)).const_mul _
  have hmain := integral_mono_ae (hφI.congr hae) hRI hpt
  have hIS : (∫ η, clampedSlope ρ p ‖η b‖ ^ (2 * Q) * (1 : ℝ) * dens η) ≤ D * x ^ (2 * Q) * ∫ η, dens η := by
    have := hD ι x Ψ hx hΨ hsl b
    simpa using this
  have hdensr : ballDensity (fun u => cutoffFactor ρ p (max u 0)) Ψ = dens := by
    funext η
    simp [hdens, ballDensity, radialWeightProd, norm_nonneg]
  have hm : 0 < x * lam / 4 := by positivity
  have hMo := hMom ι ρ (x * lam / 4) κ W d Ψ K _ hρ hm hκ (hR ρ p hρ hp) hdist hcv hWs hs0 (2 * n) b
  have hIU : (∫ η, ‖η b‖ ^ (2 * (2 * n)) * (1 : ℝ) * dens η) ≤
      Pn / (x * lam / 4) ^ (2 * n) * ∫ η, dens η := by
    unfold ballExpectation at hMo
    rw [hdensr] at hMo
    rw [div_le_iff₀ hZ] at hMo
    simpa using hMo
  unfold ballExpectation
  rw [div_le_iff₀ hZ]
  have e0 : (∫ η, B₀ * (t / 2 * 2 ^ (2 * Q) * (dens η + clampedSlope ρ p ‖η b‖ ^ (2 * Q) * (1 : ℝ) * dens η) +
      1 / (2 * t) * (‖η b‖ ^ (2 * (2 * n)) * (1 : ℝ) * dens η))) =
      B₀ * (t / 2 * 2 ^ (2 * Q) * ((∫ η, dens η) + ∫ η, clampedSlope ρ p ‖η b‖ ^ (2 * Q) * (1 : ℝ) * dens η) +
        1 / (2 * t) * ∫ η, ‖η b‖ ^ (2 * (2 * n)) * (1 : ℝ) * dens η) := by
    have i1 : Integrable fun η => t / 2 * 2 ^ (2 * Q) *
        (dens η + clampedSlope ρ p ‖η b‖ ^ (2 * Q) * (1 : ℝ) * dens η) := (hint.add hSI).const_mul _
    have i2 : Integrable fun η => 1 / (2 * t) * (‖η b‖ ^ (2 * (2 * n)) * (1 : ℝ) * dens η) :=
      hUI.const_mul _
    have i3 : (∫ η, (dens η + clampedSlope ρ p ‖η b‖ ^ (2 * Q) * (1 : ℝ) * dens η)) =
        (∫ η, dens η) + ∫ η, clampedSlope ρ p ‖η b‖ ^ (2 * Q) * (1 : ℝ) * dens η := integral_add hint hSI
    rw [integral_const_mul, integral_add i1 i2, integral_const_mul, integral_const_mul, i3]
  rw [e0] at hmain
  refine hmain.trans ?_
  set Z := ∫ η, dens η with hZd
  have hxp : 1 ≤ x ^ (2 * Q) := one_le_pow₀ hx
  have hb1 : t / 2 * 2 ^ (2 * Q) * (Z + ∫ η, clampedSlope ρ p ‖η b‖ ^ (2 * Q) * (1 : ℝ) * dens η) ≤
      2 ^ (2 * Q) * (1 + D) / 2 * (x ^ N)⁻¹ * Z := by
    have h1 : Z + ∫ η, clampedSlope ρ p ‖η b‖ ^ (2 * Q) * (1 : ℝ) * dens η ≤ (1 + D) * x ^ (2 * Q) * Z := by
      have : Z ≤ x ^ (2 * Q) * Z := by nlinarith
      nlinarith
    have e1 : t * x ^ (2 * Q) = (x ^ N)⁻¹ := by
      rw [ht, pow_add]
      field_simp
    calc _ ≤ t / 2 * 2 ^ (2 * Q) * ((1 + D) * x ^ (2 * Q) * Z) := by gcongr
      _ = 2 ^ (2 * Q) * (1 + D) / 2 * (t * x ^ (2 * Q)) * Z := by ring
      _ = _ := by rw [e1]
  have hb2 : 1 / (2 * t) * ∫ η, ‖η b‖ ^ (2 * (2 * n)) * (1 : ℝ) * dens η ≤ Mn / 2 * (x ^ N)⁻¹ * Z := by
    have e1 : 1 / (2 * t) * (Pn / (x * lam / 4) ^ (2 * n)) = Mn / 2 * (x ^ N)⁻¹ := by
      have e2 : 2 * n = 2 * Q + N + N := by omega
      have e3 : (x * lam / 4) ^ (2 * n) = x ^ (2 * Q + N) * x ^ N * (lam / 4) ^ (2 * n) := by
        rw [show x * lam / 4 = x * (lam / 4) by ring, mul_pow]
        nth_rewrite 1 [e2]
        rw [pow_add]
      have e4 : (4 / lam) ^ (2 * n) = ((lam / 4) ^ (2 * n))⁻¹ := by
        rw [← inv_pow, inv_div]
      have hxa : x ^ (2 * Q + N) ≠ 0 := by positivity
      have hxb : x ^ N ≠ 0 := by positivity
      have hla : (lam / 4) ^ (2 * n) ≠ 0 := by positivity
      rw [hMn', ht, e3, e4]
      field_simp
    calc _ ≤ 1 / (2 * t) * (Pn / (x * lam / 4) ^ (2 * n) * Z) := by gcongr
      _ = _ := by rw [← mul_assoc, e1]
  have hsum := add_le_add hb1 hb2
  calc _ ≤ B₀ * (2 ^ (2 * Q) * (1 + D) / 2 * (x ^ N)⁻¹ * Z + Mn / 2 * (x ^ N)⁻¹ * Z) := by gcongr
    _ = _ := by ring
end Moments
end YangMills.Construction.Estimates
end
