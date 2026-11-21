import YangMills.Construction.ClusterExpansionOfAStep.PartsOfTheCostAlongMoves
import YangMills.Construction.ClusterExpansionOfAStep.SecondMomentOfAConvexLawProof
import YangMills.Construction.ColdStepAtMirrorFrames.CalculusOfLocalTerms
import YangMills.Construction.ColdStepAtMirrorFrames.CovarianceOfAConvexMeasure
import YangMills.Construction.ColdStepAtMirrorFrames.MomentsOfAConvexMeasure
import YangMills.Construction.ColdStepAtMirrorFrames.RimOfACutProof
import YangMills.Construction.ColdStepAtMirrorFrames.ThirdDerivativeAlongFields
import Mathlib
set_option autoImplicit false
set_option linter.unusedSectionVars false
set_option linter.unusedVariables false
noncomputable section
open MeasureTheory
namespace YangMills.Construction.ColdStepAtMirrorFrames.ThirdDerivative
variable {ι : Type} [Fintype ι] [DecidableEq ι]
variable {ρ : ℝ} {r : ℝ → ℝ} {Ψ : BondField ι → ℝ}
theorem radialWeight_contDiff (h : IsCutoffMeasureData ρ r Ψ) : ContDiff ℝ 1 fun v : BondVector => r ‖v‖ := by
  rw [contDiff_iff_contDiffAt]
  intro v
  by_cases hv : v = 0
  · subst hv
    have : (fun v : BondVector => r ‖v‖) =ᶠ[nhds 0] fun _ => (1 : ℝ) := by
      have hb : Metric.ball (0 : BondVector) (5 * ρ / 8) ∈ nhds (0 : BondVector) :=
        Metric.ball_mem_nhds _ (by have := h.pos; positivity)
      filter_upwards [hb] with w hw
      have : ‖w‖ < 5 * ρ / 8 := by simpa using hw
      exact h.radial.one _ (norm_nonneg _) this.le
    exact contDiffAt_const.congr_of_eventuallyEq this
  · exact h.radial.smooth.contDiffAt.comp v (contDiffAt_norm ℝ hv)
theorem radialWeightProd_contDiff (h : IsCutoffMeasureData ρ r Ψ) : ContDiff ℝ 1 (radialWeightProd (ι := ι) r) := by
  unfold radialWeightProd
  apply contDiff_prod
  intro b _
  exact (radialWeight_contDiff h).comp (contDiff_apply ℝ BondVector b)
theorem radialWeight_nonneg (h : IsCutoffMeasureData ρ r Ψ) (u : ℝ) (hu : 0 ≤ u) : 0 ≤ r u := by
  rcases lt_or_ge u ρ with h' | h'
  · exact (h.radial.pos u hu h').le
  · rw [h.radial.zero u h']
theorem radialWeightProd_nonneg (h : IsCutoffMeasureData ρ r Ψ) (η : BondField ι) : 0 ≤ radialWeightProd r η :=
  Finset.prod_nonneg fun b _ => radialWeight_nonneg h _ (norm_nonneg _)
theorem inOpenBalls_of_prod_ne_zero (h : IsCutoffMeasureData ρ r Ψ) (η : BondField ι) (hη : radialWeightProd r η ≠ 0) :
    InOpenBalls ρ η := by
  intro b
  by_contra hc
  push Not at hc
  exact hη (Finset.prod_eq_zero (Finset.mem_univ b) (h.radial.zero _ hc))
theorem ballDensity_contDiff (h : IsCutoffMeasureData ρ r Ψ) : ContDiff ℝ 1 (ballDensity r Ψ) := by
  unfold ballDensity
  exact (radialWeightProd_contDiff h).mul ((h.smooth.of_le (by norm_num)).neg.exp)
theorem ballDensity_hasCompactSupport (h : IsCutoffMeasureData ρ r Ψ) : HasCompactSupport (ballDensity r Ψ) := by
  refine HasCompactSupport.intro (isCompact_closedBall (0 : BondField ι) ρ) fun η hη => ?_
  by_contra hne
  apply hη
  have hR : radialWeightProd r η ≠ 0 := fun h' => hne (by simp [ballDensity, h'])
  rw [mem_closedBall_zero_iff]
  exact (pi_norm_le_iff_of_nonneg h.pos.le).mpr fun b => (inOpenBalls_of_prod_ne_zero h η hR b).le
theorem ballDensity_nonneg (h : IsCutoffMeasureData ρ r Ψ) (η : BondField ι) :
    0 ≤ ballDensity r Ψ η :=
  mul_nonneg (radialWeightProd_nonneg h η) (Real.exp_pos _).le
theorem ballDensity_eq_zero (h : IsCutoffMeasureData ρ r Ψ) (η : BondField ι) (hη : ¬ InOpenBalls ρ η) :
    ballDensity r Ψ η = 0 := by
  by_contra hne
  exact hη (inOpenBalls_of_prod_ne_zero h η (fun h' => hne (by simp [ballDensity, h'])))
theorem integrable_mul_ballDensity (h : IsCutoffMeasureData ρ r Ψ) {f : BondField ι → ℝ} (hf : Continuous f) :
    Integrable (fun η => f η * ballDensity r Ψ η) :=
  Continuous.integrable_of_hasCompactSupport (hf.mul (ballDensity_contDiff h).continuous)
    (ballDensity_hasCompactSupport h).mul_left
theorem ballDensity_integral_pos (h : IsCutoffMeasureData ρ r Ψ) : 0 < ∫ η, ballDensity r Ψ η := by
  have hc : Continuous (ballDensity r Ψ) := (ballDensity_contDiff h).continuous
  have h0 : 0 < ballDensity r Ψ 0 := by
    unfold ballDensity radialWeightProd
    refine mul_pos (Finset.prod_pos fun b _ => ?_) (Real.exp_pos _)
    simpa using h.radial.pos ‖(0 : BondField ι) b‖ (norm_nonneg _) (by simpa using h.pos)
  exact hc.integral_pos_of_hasCompactSupport_nonneg_nonzero (μ := volume) (ballDensity_hasCompactSupport h)
    (ballDensity_nonneg h) h0.ne'
theorem ballExpectation_def (f : BondField ι → ℝ) : ballExpectation r Ψ f =
    (∫ η, f η * ballDensity r Ψ η) / ∫ η, ballDensity r Ψ η := rfl
theorem ballExpectation_add (h : IsCutoffMeasureData ρ r Ψ) {f g : BondField ι → ℝ} (hf : Continuous f)
    (hg : Continuous g) :
    ballExpectation r Ψ (fun η => f η + g η) = ballExpectation r Ψ f + ballExpectation r Ψ g := by
  simp only [ballExpectation_def, add_mul]
  rw [integral_add (integrable_mul_ballDensity h hf) (integrable_mul_ballDensity h hg), add_div]
theorem ballExpectation_const_mul (c : ℝ) (f : BondField ι → ℝ) :
    ballExpectation r Ψ (fun η => c * f η) = c * ballExpectation r Ψ f := by
  simp only [ballExpectation_def, mul_assoc]
  rw [integral_const_mul, mul_div_assoc]
theorem ballExpectation_sub (h : IsCutoffMeasureData ρ r Ψ) {f g : BondField ι → ℝ} (hf : Continuous f)
    (hg : Continuous g) :
    ballExpectation r Ψ (fun η => f η - g η) = ballExpectation r Ψ f - ballExpectation r Ψ g := by
  simp only [ballExpectation_def, sub_mul]
  rw [integral_sub (integrable_mul_ballDensity h hf) (integrable_mul_ballDensity h hg), sub_div]
theorem ballExpectation_const (h : IsCutoffMeasureData ρ r Ψ) (c : ℝ) :
    ballExpectation r Ψ (fun _ : BondField ι => c) = c := by
  simp only [ballExpectation_def]
  rw [integral_const_mul, mul_div_assoc, div_self (ballDensity_integral_pos h).ne', mul_one]
theorem ballExpectation_nonneg (h : IsCutoffMeasureData ρ r Ψ) {f : BondField ι → ℝ}
    (hf : ∀ η, InOpenBalls ρ η → 0 ≤ f η) : 0 ≤ ballExpectation r Ψ f := by
  rw [ballExpectation_def]
  apply div_nonneg _ (ballDensity_integral_pos h).le
  apply integral_nonneg
  intro η
  by_cases hη : InOpenBalls ρ η
  · exact mul_nonneg (hf η hη) (ballDensity_nonneg h η)
  · simp [ballDensity_eq_zero h η hη]
theorem ballExpectation_mono (h : IsCutoffMeasureData ρ r Ψ) {f g : BondField ι → ℝ} (hf : Continuous f)
    (hg : Continuous g) (hfg : ∀ η, InOpenBalls ρ η → f η ≤ g η) :
    ballExpectation r Ψ f ≤ ballExpectation r Ψ g := by
  have := ballExpectation_nonneg h (f := fun η => g η - f η) fun η hη => sub_nonneg.mpr (hfg η hη)
  rw [ballExpectation_sub h hg hf] at this
  linarith
theorem ballCovariance_eq (h : IsCutoffMeasureData ρ r Ψ) {f g : BondField ι → ℝ} (hf : Continuous f)
    (hg : Continuous g) :
    ballCovariance r Ψ f g = ballExpectation r Ψ (fun η => (f η - ballExpectation r Ψ f) * g η) := by
  unfold ballCovariance
  have e : (fun η => (f η - ballExpectation r Ψ f) * g η) =
      fun η => f η * g η - ballExpectation r Ψ f * g η := by
    funext η
    ring
  rw [e, ballExpectation_sub h (f := fun η => f η * g η) (g := fun η => ballExpectation r Ψ f * g η)
    (by fun_prop) (by fun_prop), ballExpectation_const_mul]
theorem ballExpectation_mul_sq_le (h : IsCutoffMeasureData ρ r Ψ) {f g : BondField ι → ℝ} (hf : Continuous f)
    (hg : Continuous g) :
    ballExpectation r Ψ (fun η => f η * g η) ^ 2 ≤
      ballExpectation r Ψ (fun η => f η ^ 2) * ballExpectation r Ψ (fun η => g η ^ 2) := by
  set A := ballExpectation r Ψ (fun η => f η ^ 2) with hA
  set B := ballExpectation r Ψ (fun η => f η * g η) with hB
  set C := ballExpectation r Ψ (fun η => g η ^ 2) with hC
  have key : ∀ s t : ℝ, 0 ≤ s ^ 2 * A + 2 * s * t * B + t ^ 2 * C := by
    intro s t
    have h1 : 0 ≤ ballExpectation r Ψ (fun η => (s * f η + t * g η) ^ 2) :=
      ballExpectation_nonneg h fun η _ => sq_nonneg _
    have e : (fun η => (s * f η + t * g η) ^ 2) = fun η =>
        s ^ 2 * f η ^ 2 + ((2 * s * t) * (f η * g η) + t ^ 2 * g η ^ 2) := by
      funext η
      ring
    rw [e, ballExpectation_add h (f := fun η => s ^ 2 * f η ^ 2)
      (g := fun η => (2 * s * t) * (f η * g η) + t ^ 2 * g η ^ 2) (by fun_prop) (by fun_prop),
      ballExpectation_add h (f := fun η => (2 * s * t) * (f η * g η)) (g := fun η => t ^ 2 * g η ^ 2)
        (by fun_prop) (by fun_prop),
      ballExpectation_const_mul, ballExpectation_const_mul, ballExpectation_const_mul] at h1
    linarith
  have hA0 : 0 ≤ A := ballExpectation_nonneg h fun η _ => sq_nonneg _
  have hC0 : 0 ≤ C := ballExpectation_nonneg h fun η _ => sq_nonneg _
  rcases hA0.lt_or_eq with hpos | hz
  · nlinarith [key B (-A)]
  · have hB0 : B = 0 := by
      by_contra hne
      have h2 := key (-(C + 1) / (2 * B)) 1
      rw [← hz] at h2
      have e : 2 * (-(C + 1) / (2 * B)) * 1 * B = -(C + 1) := by
        field_simp
      nlinarith
    rw [hB0, ← hz]
    simp
theorem ballL2Norm_nonneg (h : BondField ι → ℝ) : 0 ≤ ballL2Norm r Ψ h := Real.sqrt_nonneg _
theorem ballL2Norm_sq (hd : IsCutoffMeasureData ρ r Ψ) (h : BondField ι → ℝ) :
    ballL2Norm r Ψ h ^ 2 = ballExpectation r Ψ fun η => h η ^ 2 :=
  Real.sq_sqrt (ballExpectation_nonneg hd fun _ _ => sq_nonneg _)
theorem abs_ballExpectation_mul_le (h : IsCutoffMeasureData ρ r Ψ) {f g : BondField ι → ℝ} (hf : Continuous f)
    (hg : Continuous g) :
    |ballExpectation r Ψ (fun η => f η * g η)| ≤ ballL2Norm r Ψ f * ballL2Norm r Ψ g := by
  have h1 := ballExpectation_mul_sq_le h hf hg
  have h2 : 0 ≤ ballExpectation r Ψ (fun η => f η ^ 2) := ballExpectation_nonneg h fun _ _ => sq_nonneg _
  unfold ballL2Norm
  rw [← Real.sqrt_mul h2]
  exact Real.abs_le_sqrt h1
theorem ballL2Norm_add_le (h : IsCutoffMeasureData ρ r Ψ) {f g : BondField ι → ℝ} (hf : Continuous f)
    (hg : Continuous g) :
    ballL2Norm r Ψ (fun η => f η + g η) ≤ ballL2Norm r Ψ f + ballL2Norm r Ψ g := by
  have hn : 0 ≤ ballL2Norm r Ψ f + ballL2Norm r Ψ g := add_nonneg (ballL2Norm_nonneg _) (ballL2Norm_nonneg _)
  unfold ballL2Norm
  rw [Real.sqrt_le_iff]
  refine ⟨hn, ?_⟩
  have e : (fun η => (f η + g η) ^ 2) = fun η => f η ^ 2 + (2 * (f η * g η) + g η ^ 2) := by
    funext η
    ring
  rw [e, ballExpectation_add h (f := fun η => f η ^ 2) (g := fun η => 2 * (f η * g η) + g η ^ 2)
      (by fun_prop) (by fun_prop),
    ballExpectation_add h (f := fun η => 2 * (f η * g η)) (g := fun η => g η ^ 2) (by fun_prop) (by fun_prop),
    ballExpectation_const_mul]
  change _ ≤ (ballL2Norm r Ψ f + ballL2Norm r Ψ g) ^ 2
  have h1 := (abs_le.mp (abs_ballExpectation_mul_le h hf hg)).2
  have h2 := ballL2Norm_sq h f
  have h3 := ballL2Norm_sq h g
  nlinarith
theorem ballL2Norm_le_of_abs_le (h : IsCutoffMeasureData ρ r Ψ) {f g : BondField ι → ℝ} (hf : Continuous f)
    (hg : Continuous g) (hfg : ∀ η, InOpenBalls ρ η → |f η| ≤ |g η|) :
    ballL2Norm r Ψ f ≤ ballL2Norm r Ψ g := by
  apply Real.sqrt_le_sqrt
  apply ballExpectation_mono h (hf.pow 2) (hg.pow 2)
  intro η hη
  exact sq_le_sq.mpr (hfg η hη)
theorem ballL2Norm_const (h : IsCutoffMeasureData ρ r Ψ) {c : ℝ} (hc : 0 ≤ c) :
    ballL2Norm r Ψ (fun _ : BondField ι => c) = c := by
  unfold ballL2Norm
  rw [ballExpectation_const h, Real.sqrt_sq hc]
theorem ballL2Norm_le_const (h : IsCutoffMeasureData ρ r Ψ) {f : BondField ι → ℝ} (hf : Continuous f)
    {c : ℝ} (hc : 0 ≤ c) (hfc : ∀ η, InOpenBalls ρ η → |f η| ≤ c) : ballL2Norm r Ψ f ≤ c := by
  have := ballL2Norm_le_of_abs_le h hf (continuous_const (y := c)) fun η hη => by
    rw [abs_of_nonneg hc]
    exact hfc η hη
  rwa [ballL2Norm_const h hc] at this
theorem ballL2Norm_const_mul (h : IsCutoffMeasureData ρ r Ψ) (c : ℝ) (f : BondField ι → ℝ) :
    ballL2Norm r Ψ (fun η => c * f η) = |c| * ballL2Norm r Ψ f := by
  unfold ballL2Norm
  have e : (fun η => (c * f η) ^ 2) = fun η => c ^ 2 * f η ^ 2 := by
    funext η
    ring
  rw [e, ballExpectation_const_mul, Real.sqrt_mul (sq_nonneg c), Real.sqrt_sq_eq_abs]
theorem abs_ballExpectation_le_ballL2Norm (h : IsCutoffMeasureData ρ r Ψ) {f : BondField ι → ℝ} (hf : Continuous f) :
    |ballExpectation r Ψ f| ≤ ballL2Norm r Ψ f := by
  have h1 := abs_ballExpectation_mul_le h hf (continuous_const (y := (1 : ℝ)))
  simp only [mul_one] at h1
  rwa [ballL2Norm_const h zero_le_one, mul_one] at h1
end YangMills.Construction.ColdStepAtMirrorFrames.ThirdDerivative
end
noncomputable section
open Set
namespace YangMills.Construction.ColdStepAtMirrorFrames.ThirdDerivative
theorem deriv_nonneg_of_monotoneOn {f : ℝ → ℝ} {d u a b : ℝ} (hf : HasDerivAt f d u) (hu : u ∈ Ioo a b)
    (hm : MonotoneOn f (Ioo a b)) : 0 ≤ d := by
  have h1 := hasDerivAt_iff_tendsto_slope.mp hf
  refine ge_of_tendsto h1 ?_
  have hn : Ioo a b ∈ nhds u := Ioo_mem_nhds hu.1 hu.2
  filter_upwards [mem_nhdsWithin_of_mem_nhds hn, self_mem_nhdsWithin] with v hv hne
  rw [slope_def_field]
  rcases lt_or_gt_of_ne hne with h | h
  · apply div_nonneg_of_nonpos
    · linarith [hm hv hu h.le]
    · linarith
  · apply div_nonneg
    · linarith [hm hu hv h.le]
    · linarith
variable {ρ : ℝ} {p : ℝ → ℝ}
def cutoffSlope (ρ : ℝ) (p : ℝ → ℝ) (u : ℝ) : ℝ := if u ≤ ρ / 2 then 0 else deriv p u
def cutoffCurvature (ρ : ℝ) (p : ℝ → ℝ) (u : ℝ) : ℝ := if u ≤ ρ / 2 then 0 else deriv (deriv p) u
theorem cutoff_hasDerivAt (hp : IsCutoff ρ p) {u : ℝ} (h0 : 0 < u) (h1 : u < ρ) :
    HasDerivAt p (deriv p u) u := by apply _root_.YangMills.Construction.ColdStepAtMirrorFrames.CutoffFactor.cutoff_hasDerivAt <;> assumption
theorem cutoff_deriv_contDiffOn (hp : IsCutoff ρ p) :
    ContDiffOn ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) (deriv p) (Ioo 0 ρ) := by apply _root_.YangMills.Construction.ColdStepAtMirrorFrames.CutoffFactor.cutoff_deriv_contDiffOn <;> assumption
theorem cutoff_deriv2_contDiffOn (hp : IsCutoff ρ p) :
    ContDiffOn ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) (deriv (deriv p)) (Ioo 0 ρ) :=
  ((contDiffOn_infty_iff_deriv_of_isOpen isOpen_Ioo).mp (cutoff_deriv_contDiffOn hp)).2
theorem cutoff_deriv_hasDerivAt (hp : IsCutoff ρ p) {u : ℝ} (h0 : 0 < u) (h1 : u < ρ) :
    HasDerivAt (deriv p) (deriv (deriv p) u) u := by apply _root_.YangMills.Construction.ColdStepAtMirrorFrames.CutoffFactor.cutoff_hasDerivAt_deriv <;> assumption
theorem cutoff_deriv_eq_zero_inner (hρ : 0 < ρ) (hp : IsCutoff ρ p) {u : ℝ} (h0 : 0 < u) (h1 : u < 5 * ρ / 8) :
    deriv p u = 0 := by
  have hev : p =ᶠ[nhds u] fun _ => 0 := by
    filter_upwards [Ioo_mem_nhds h0 h1] with v hv
    exact hp.vanish_small v hv.1.le hv.2.le
  rw [hev.deriv_eq]
  simp
theorem cutoff_deriv2_eq_zero_inner (hρ : 0 < ρ) (hp : IsCutoff ρ p) {u : ℝ} (h0 : 0 < u) (h1 : u < 5 * ρ / 8) :
    deriv (deriv p) u = 0 := by
  have hev : deriv p =ᶠ[nhds u] fun _ => 0 := by
    filter_upwards [Ioo_mem_nhds h0 h1] with v hv
    exact cutoff_deriv_eq_zero_inner hρ hp hv.1 hv.2
  rw [hev.deriv_eq]
  simp
theorem cutoffSlope_inner (hρ : 0 < ρ) (hp : IsCutoff ρ p) {u : ℝ} (h1 : u < 5 * ρ / 8) : cutoffSlope ρ p u = 0 := by
  unfold cutoffSlope
  split_ifs with h
  · rfl
  · exact cutoff_deriv_eq_zero_inner hρ hp (by push Not at h; linarith) h1
theorem cutoffCurvature_inner (hρ : 0 < ρ) (hp : IsCutoff ρ p) {u : ℝ} (h1 : u < 5 * ρ / 8) : cutoffCurvature ρ p u = 0 := by
  unfold cutoffCurvature
  split_ifs with h
  · rfl
  · exact cutoff_deriv2_eq_zero_inner hρ hp (by push Not at h; linarith) h1
theorem cutoffSlope_outer (hρ : 0 < ρ) {u : ℝ} (h : ρ / 2 < u) : cutoffSlope ρ p u = deriv p u := by
  unfold cutoffSlope
  rw [if_neg (by linarith)]
theorem cutoffCurvature_outer (hρ : 0 < ρ) {u : ℝ} (h : ρ / 2 < u) : cutoffCurvature ρ p u = deriv (deriv p) u := by
  unfold cutoffCurvature
  rw [if_neg (by linarith)]
theorem cutoffSlope_hasDerivAt (hρ : 0 < ρ) (hp : IsCutoff ρ p) {u : ℝ} (h1 : u < ρ) :
    HasDerivAt (cutoffSlope ρ p) (cutoffCurvature ρ p u) u := by
  rcases lt_or_ge u (5 * ρ / 8) with h | h
  · have hev : cutoffSlope ρ p =ᶠ[nhds u] fun _ => 0 := by
      filter_upwards [Iio_mem_nhds h] with v hv
      exact cutoffSlope_inner hρ hp hv
    rw [cutoffCurvature_inner hρ hp h]
    exact (hasDerivAt_const u (0 : ℝ)).congr_of_eventuallyEq hev
  · have hu : ρ / 2 < u := by linarith
    have hev : cutoffSlope ρ p =ᶠ[nhds u] deriv p := by
      filter_upwards [Ioi_mem_nhds hu] with v hv
      exact cutoffSlope_outer hρ hv
    rw [cutoffCurvature_outer hρ hu]
    exact (cutoff_deriv_hasDerivAt hp (by linarith) h1).congr_of_eventuallyEq hev
theorem cutoffCurvature_continuousAt (hρ : 0 < ρ) (hp : IsCutoff ρ p) {u : ℝ} (h1 : u < ρ) :
    ContinuousAt (cutoffCurvature ρ p) u := by
  rcases lt_or_ge u (5 * ρ / 8) with h | h
  · have hev : cutoffCurvature ρ p =ᶠ[nhds u] fun _ => 0 := by
      filter_upwards [Iio_mem_nhds h] with v hv
      exact cutoffCurvature_inner hρ hp hv
    exact continuousAt_const.congr hev.symm
  · have hu : ρ / 2 < u := by linarith
    have hev : cutoffCurvature ρ p =ᶠ[nhds u] deriv (deriv p) := by
      filter_upwards [Ioi_mem_nhds hu] with v hv
      exact cutoffCurvature_outer hρ hv
    have : ContinuousAt (deriv (deriv p)) u :=
      ((cutoff_deriv2_contDiffOn hp).contDiffAt (Ioo_mem_nhds (by linarith) h1)).continuousAt
    exact this.congr hev.symm
theorem cutoffSlope_contDiffAt (hρ : 0 < ρ) (hp : IsCutoff ρ p) {u : ℝ} (h1 : u < ρ) :
    ContDiffAt ℝ 1 (cutoffSlope ρ p) u := by
  have hn : Iio ρ ∈ nhds u := Iio_mem_nhds h1
  have : ContDiffOn ℝ ((0 : WithTop ℕ∞) + 1) (cutoffSlope ρ p) (Iio ρ) := by
    rw [contDiffOn_succ_iff_deriv_of_isOpen isOpen_Iio]
    refine ⟨?_, by simp, ?_⟩
    · intro v hv
      exact (cutoffSlope_hasDerivAt hρ hp hv).differentiableAt.differentiableWithinAt
    · rw [contDiffOn_zero]
      intro v hv
      have hev : deriv (cutoffSlope ρ p) =ᶠ[nhds v] cutoffCurvature ρ p := by
        filter_upwards [Iio_mem_nhds hv] with w hw
        exact (cutoffSlope_hasDerivAt hρ hp hw).deriv
      exact ((cutoffCurvature_continuousAt hρ hp hv).congr hev.symm).continuousWithinAt
  simpa using this.contDiffAt hn
theorem cutoff_deriv_monotoneOn (hp : IsCutoff ρ p) : MonotoneOn (deriv p) (Ioo 0 ρ) :=
  (hp.convex.subset Ioo_subset_Ico_self (convex_Ioo 0 ρ)).monotoneOn_deriv
    fun x hx => (cutoff_hasDerivAt hp hx.1 hx.2).differentiableAt
theorem cutoffSlope_nonneg (hρ : 0 < ρ) (hp : IsCutoff ρ p) {u : ℝ} (h1 : u < ρ) : 0 ≤ cutoffSlope ρ p u := by
  rcases lt_or_ge u (5 * ρ / 8) with h | h
  · rw [cutoffSlope_inner hρ hp h]
  · rw [cutoffSlope_outer hρ (by linarith)]
    have := cutoff_deriv_monotoneOn hp (a := ρ / 2) (b := u) ⟨by linarith, by linarith⟩ ⟨by linarith, h1⟩
      (by linarith)
    rwa [cutoff_deriv_eq_zero_inner hρ hp (by linarith) (by linarith)] at this
theorem cutoffCurvature_nonneg (hρ : 0 < ρ) (hp : IsCutoff ρ p) {u : ℝ} (h1 : u < ρ) : 0 ≤ cutoffCurvature ρ p u := by
  rcases lt_or_ge u (5 * ρ / 8) with h | h
  · rw [cutoffCurvature_inner hρ hp h]
  · rw [cutoffCurvature_outer hρ (by linarith)]
    exact deriv_nonneg_of_monotoneOn (cutoff_deriv_hasDerivAt hp (by linarith) h1) ⟨by linarith, h1⟩ (cutoff_deriv_monotoneOn hp)
theorem eq_of_hasDerivAt_zero_Ioo {g : ℝ → ℝ} {c d : ℝ} (hd : ∀ u ∈ Ioo c d, HasDerivAt g 0 u) {u v : ℝ}
    (hu : u ∈ Ioo c d) (hv : v ∈ Ioo c d) : g u = g v := by apply _root_.YangMills.Construction.ColdStepAtMirrorFrames.CutoffFactor.eq_of_hasDerivAt_zero_on_Ioo <;> assumption
theorem cutoff_deriv_form_near_edge (hρ : 0 < ρ) (hp : IsCutoff ρ p) : ∃ c A : ℝ, 0 < c ∧ c < ρ ∧
    ∀ u ∈ Ioo c ρ, deriv p u = ((ρ - u) ^ 3)⁻¹ / 3 + A ∧ deriv (deriv p) u = ((ρ - u) ^ 4)⁻¹ := by
  obtain ⟨u₀, hu₀, hrim⟩ := hp.rim_second_deriv
  set c := max u₀ (ρ / 2) with hc
  have hc0 : 0 < c := lt_of_lt_of_le (by positivity) (le_max_right _ _)
  have hcρ : c < ρ := max_lt hu₀ (by linarith)
  set um := (c + ρ) / 2 with hum
  have humI : um ∈ Ioo c ρ := ⟨by simp only [hum]; linarith, by simp only [hum]; linarith⟩
  have hi : ∀ u ∈ Ioo c ρ, 0 < ρ - u := fun u hu => by linarith [hu.2]
  have hd3 : ∀ u ∈ Ioo c ρ, HasDerivAt (fun v => ((ρ - v) ^ 3)⁻¹ / 3) (((ρ - u) ^ 4)⁻¹) u := by
    intro u hu
    have h1 : HasDerivAt (fun v : ℝ => (ρ - v) ^ 3) (3 * (ρ - u) ^ 2 * (-1)) u := by
      have := ((hasDerivAt_id u).const_sub ρ).fun_pow 3
      exact HasDerivAt.congr_deriv this (by simp)
    have hne : (ρ - u) ^ 3 ≠ 0 := (pow_pos (hi u hu) 3).ne'
    refine HasDerivAt.congr_deriv ((h1.fun_inv hne).div_const 3) ?_
    have := hi u hu
    field_simp
    try ring
  set A := deriv p um - ((ρ - um) ^ 3)⁻¹ / 3 with hA
  have h2nd : ∀ v ∈ Ioo c ρ, deriv (deriv p) v = ((ρ - v) ^ 4)⁻¹ := fun v hv =>
    hrim v (lt_of_le_of_lt (le_max_left _ _) hv.1) hv.2
  refine ⟨c, A, hc0, hcρ, fun u hu => ⟨?_, h2nd u hu⟩⟩
  have hz : ∀ v ∈ Ioo c ρ, HasDerivAt (fun w => deriv p w - ((ρ - w) ^ 3)⁻¹ / 3) 0 v := by
    intro v hv
    have h1 := cutoff_deriv_hasDerivAt hp (hc0.trans hv.1) hv.2
    rw [h2nd v hv] at h1
    exact HasDerivAt.congr_deriv (h1.sub (hd3 v hv)) (by ring)
  have := eq_of_hasDerivAt_zero_Ioo hz hu humI
  simp only [hA]
  linarith
theorem cutoffCurvature_le (hρ : 0 < ρ) (hp : IsCutoff ρ p) {δ : ℝ} (hδ : 0 < δ) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ u, u < ρ → cutoffCurvature ρ p u ≤ δ * cutoffSlope ρ p u ^ 2 + C := by
  obtain ⟨c, A, hc0, hcρ, hform⟩ := cutoff_deriv_form_near_edge hρ hp
  set t₀ := min (min 1 ((ρ - c) / 2)) (min (1 / (6 * |A| + 1)) (δ / 36)) with ht₀
  have hpos : 0 < t₀ := by
    have : 0 < ρ - c := by linarith
    have h6 : 0 < 6 * |A| + 1 := by positivity
    simp only [ht₀]
    positivity
  have ht1 : t₀ ≤ 1 := (min_le_left _ _).trans (min_le_left _ _)
  have ht2 : t₀ ≤ (ρ - c) / 2 := (min_le_left _ _).trans (min_le_right _ _)
  have ht3 : t₀ ≤ 1 / (6 * |A| + 1) := (min_le_right _ _).trans (min_le_left _ _)
  have ht4 : t₀ ≤ δ / 36 := (min_le_right _ _).trans (min_le_right _ _)
  have hcomp : IsCompact (Icc c (ρ - t₀)) := isCompact_Icc
  have hcont : ContinuousOn (deriv (deriv p)) (Icc c (ρ - t₀)) :=
    (cutoff_deriv2_contDiffOn hp).continuousOn.mono fun v hv => ⟨by linarith [hv.1], by linarith [hv.2]⟩
  obtain ⟨M, hM⟩ := hcomp.exists_bound_of_continuousOn hcont
  have hcomp2 : IsCompact (Icc (ρ / 2) (ρ - t₀)) := isCompact_Icc
  have hcont2 : ContinuousOn (deriv (deriv p)) (Icc (ρ / 2) (ρ - t₀)) :=
    (cutoff_deriv2_contDiffOn hp).continuousOn.mono fun v hv => ⟨by linarith [hv.1], by linarith [hv.2]⟩
  obtain ⟨M2, hM2⟩ := hcomp2.exists_bound_of_continuousOn hcont2
  refine ⟨|M2|, abs_nonneg _, fun u hu => ?_⟩
  by_cases h1 : u ≤ ρ / 2
  · simp only [cutoffCurvature, if_pos h1, cutoffSlope]
    positivity
  push Not at h1
  rw [cutoffCurvature_outer hρ h1, cutoffSlope_outer hρ h1]
  by_cases h2 : u ≤ ρ - t₀
  · have := hM2 u ⟨h1.le, h2⟩
    have h3 := (abs_le.mp this).2
    have := le_abs_self M2
    have := sq_nonneg (deriv p u)
    simp only [Real.norm_eq_abs] at *
    nlinarith [mul_nonneg hδ.le (sq_nonneg (deriv p u)), (le_abs_self (deriv (deriv p) u))]
  · push Not at h2
    have huc : u ∈ Ioo c ρ := ⟨by linarith, hu⟩
    obtain ⟨e1, e2⟩ := hform u huc
    set t := ρ - u with ht
    have ht0 : 0 < t := by simp only [ht]; linarith
    have htt : t < t₀ := by simp only [ht]; linarith
    have hy : (1 : ℝ) ≤ (t ^ 3)⁻¹ * t ^ 3 := by
      rw [inv_mul_cancel₀ (by positivity)]
    set y := (t ^ 3)⁻¹ with hydef
    have hy0 : 0 < y := by positivity
    have ht1' : t < 1 := lt_of_lt_of_le htt ht1
    have ht3' : t * (6 * |A| + 1) ≤ 1 := by
      have h6 : 0 < 6 * |A| + 1 := by positivity
      have : t ≤ 1 / (6 * |A| + 1) := (htt.le).trans ht3
      rwa [le_div_iff₀ h6] at this
    have hyA : 6 * |A| ≤ y := by
      have h3 : t ^ 3 ≤ t := by nlinarith [pow_pos ht0 2, sq_nonneg t, pow_le_one₀ ht0.le ht1'.le (n := 2)]
      have : y * t ≥ 1 := by
        have : y * t ^ 3 = 1 := by rw [hydef]; field_simp
        nlinarith
      nlinarith [abs_nonneg A]
    have hsl : y / 6 ≤ deriv p u := by
      rw [e1]
      have := neg_abs_le A
      linarith
    have hsq : (y / 6) ^ 2 ≤ deriv p u ^ 2 := by
      apply pow_le_pow_left₀ (by positivity) hsl
    have hcur : (t ^ 4)⁻¹ ≤ δ * (y / 6) ^ 2 := by
      have e3 : y ^ 2 = (t ^ 4)⁻¹ * (t ^ 2)⁻¹ := by
        rw [hydef]
        field_simp
      have h36 : 36 * t ^ 2 ≤ δ := by
        have : t ≤ δ / 36 := htt.le.trans ht4
        nlinarith
      have hq : 0 < (t ^ 4)⁻¹ := by positivity
      have h4 : 36 ≤ δ * (t ^ 2)⁻¹ := by
        rw [← div_eq_mul_inv, le_div_iff₀ (by positivity)]
        exact h36
      calc (t ^ 4)⁻¹ = (t ^ 4)⁻¹ * 36 / 36 := by ring
        _ ≤ (t ^ 4)⁻¹ * (δ * (t ^ 2)⁻¹) / 36 := by
            apply div_le_div_of_nonneg_right _ (by norm_num)
            exact mul_le_mul_of_nonneg_left h4 hq.le
        _ = δ * (y / 6) ^ 2 := by
            rw [div_pow, e3]
            ring
    rw [e2]
    have : δ * (y / 6) ^ 2 ≤ δ * deriv p u ^ 2 := mul_le_mul_of_nonneg_left hsq hδ.le
    have := abs_nonneg M2
    linarith
end YangMills.Construction.ColdStepAtMirrorFrames.ThirdDerivative
end
noncomputable section
open Set
namespace YangMills.Construction.ColdStepAtMirrorFrames.ThirdDerivative
def smoothStep (s : ℝ) : ℝ := Real.smoothTransition (s - 1)
def smoothStepScaledDeriv (s : ℝ) : ℝ := s * deriv smoothStep s
def smoothStepMulDeriv (s : ℝ) : ℝ := smoothStep s + smoothStepScaledDeriv s
abbrev smoothOrder : WithTop ℕ∞ := ((⊤ : ℕ∞) : WithTop ℕ∞)
theorem smoothStep_contDiff : ContDiff ℝ smoothOrder smoothStep :=
  Real.smoothTransition.contDiff.comp (contDiff_id.sub contDiff_const)
theorem smoothStep_deriv_contDiff : ContDiff ℝ smoothOrder (deriv smoothStep) :=
  (contDiff_infty_iff_deriv.mp smoothStep_contDiff).2
theorem smoothStepScaledDeriv_contDiff : ContDiff ℝ smoothOrder smoothStepScaledDeriv := contDiff_id.mul smoothStep_deriv_contDiff
theorem smoothStepMulDeriv_contDiff : ContDiff ℝ smoothOrder smoothStepMulDeriv := smoothStep_contDiff.add smoothStepScaledDeriv_contDiff
theorem smoothStepMulDeriv_deriv_contDiff : ContDiff ℝ smoothOrder (deriv smoothStepMulDeriv) :=
  (contDiff_infty_iff_deriv.mp smoothStepMulDeriv_contDiff).2
theorem smoothStep_of_le_one {s : ℝ} (h : s ≤ 1) : smoothStep s = 0 :=
  Real.smoothTransition.zero_of_nonpos (by linarith)
theorem smoothStep_of_two_le {s : ℝ} (h : 2 ≤ s) : smoothStep s = 1 :=
  Real.smoothTransition.one_of_one_le (by linarith)
theorem smoothStep_nonneg (s : ℝ) : 0 ≤ smoothStep s := Real.smoothTransition.nonneg _
theorem smoothStep_le_one (s : ℝ) : smoothStep s ≤ 1 := Real.smoothTransition.le_one _
theorem smoothStep_monotone : Monotone smoothStep := fun _ _ h =>
  Real.smoothTransition.monotone (by linarith)
theorem smoothStep_deriv_of_lt_one {s : ℝ} (h : s < 1) : deriv smoothStep s = 0 := by
  have hev : smoothStep =ᶠ[nhds s] fun _ => 0 := by
    filter_upwards [Iio_mem_nhds h] with v hv
    exact smoothStep_of_le_one (le_of_lt hv)
  rw [hev.deriv_eq]
  simp
theorem smoothStep_deriv_of_two_lt {s : ℝ} (h : 2 < s) : deriv smoothStep s = 0 := by
  have hev : smoothStep =ᶠ[nhds s] fun _ => 1 := by
    filter_upwards [Ioi_mem_nhds h] with v hv
    exact smoothStep_of_two_le (le_of_lt hv)
  rw [hev.deriv_eq]
  simp
theorem smoothStep_deriv_nonneg (s : ℝ) : 0 ≤ deriv smoothStep s :=
  deriv_nonneg_of_monotoneOn ((smoothStep_contDiff.differentiable (by simp)) s).hasDerivAt
    (a := s - 1) (b := s + 1) ⟨by linarith, by linarith⟩ (smoothStep_monotone.monotoneOn _)
theorem smoothStepScaledDeriv_nonneg {s : ℝ} (h : 0 ≤ s) : 0 ≤ smoothStepScaledDeriv s := mul_nonneg h (smoothStep_deriv_nonneg s)
theorem smoothStepMulDeriv_of_lt_one {s : ℝ} (h : s < 1) : smoothStepMulDeriv s = 0 := by
  simp [smoothStepMulDeriv, smoothStepScaledDeriv, smoothStep_of_le_one h.le, smoothStep_deriv_of_lt_one h]
theorem smoothStepScaledDeriv_of_lt_one {s : ℝ} (h : s < 1) : smoothStepScaledDeriv s = 0 := by
  simp [smoothStepScaledDeriv, smoothStep_deriv_of_lt_one h]
theorem smoothStepMulDeriv_deriv_of_lt_one {s : ℝ} (h : s < 1) : deriv smoothStepMulDeriv s = 0 := by
  have hev : smoothStepMulDeriv =ᶠ[nhds s] fun _ => 0 := by
    filter_upwards [Iio_mem_nhds h] with v hv
    exact smoothStepMulDeriv_of_lt_one hv
  rw [hev.deriv_eq]
  simp
theorem smoothStepMulDeriv_deriv_of_two_lt {s : ℝ} (h : 2 < s) : deriv smoothStepMulDeriv s = 0 := by
  have hev : smoothStepMulDeriv =ᶠ[nhds s] fun _ => 1 := by
    filter_upwards [Ioi_mem_nhds h] with v hv
    simp [smoothStepMulDeriv, smoothStepScaledDeriv, smoothStep_of_two_le (le_of_lt hv), smoothStep_deriv_of_two_lt hv]
  rw [hev.deriv_eq]
  simp
theorem smoothStepScaledDeriv_of_two_lt {s : ℝ} (h : 2 < s) : smoothStepScaledDeriv s = 0 := by
  simp [smoothStepScaledDeriv, smoothStep_deriv_of_two_lt h]
theorem smoothStepMulDeriv_of_two_lt {s : ℝ} (h : 2 < s) : smoothStepMulDeriv s = 1 := by
  simp [smoothStepMulDeriv, smoothStepScaledDeriv_of_two_lt h, smoothStep_of_two_le h.le]
theorem smoothStep_bounds : ∃ c : ℝ, 1 ≤ c ∧ ∀ s : ℝ, |smoothStepMulDeriv s| ≤ c * smoothStep (2 * s) ∧
    smoothStepScaledDeriv s ≤ c * smoothStep (2 * s) ∧ |deriv smoothStepMulDeriv s * s| ≤ c * smoothStep (2 * s) := by
  have hc : IsCompact (Icc (1 : ℝ) 2) := isCompact_Icc
  obtain ⟨M1, h1⟩ := hc.exists_bound_of_continuousOn smoothStepMulDeriv_contDiff.continuous.continuousOn
  obtain ⟨M2, h2⟩ := hc.exists_bound_of_continuousOn smoothStepScaledDeriv_contDiff.continuous.continuousOn
  obtain ⟨M3, h3⟩ := hc.exists_bound_of_continuousOn
    ((smoothStepMulDeriv_deriv_contDiff.continuous.mul continuous_id).continuousOn (s := Icc (1 : ℝ) 2))
  refine ⟨1 + |M1| + |M2| + |M3|, by linarith [abs_nonneg M1, abs_nonneg M2, abs_nonneg M3],
    fun s => ?_⟩
  have a1 := abs_nonneg M1
  have a2 := abs_nonneg M2
  have a3 := abs_nonneg M3
  rcases lt_or_ge s 1 with hs | hs
  · have hz : 0 ≤ smoothStep (2 * s) := smoothStep_nonneg _
    have hp : 0 ≤ (1 + |M1| + |M2| + |M3|) * smoothStep (2 * s) := by positivity
    simp only [smoothStepMulDeriv_of_lt_one hs, smoothStepScaledDeriv_of_lt_one hs, smoothStepMulDeriv_deriv_of_lt_one hs, abs_zero, zero_mul]
    exact ⟨hp, hp, hp⟩
  · have h2s : smoothStep (2 * s) = 1 := smoothStep_of_two_le (by linarith)
    rw [h2s, mul_one]
    rcases le_or_gt s 2 with hs2 | hs2
    · have b1 := h1 s ⟨hs, hs2⟩
      have b2 := h2 s ⟨hs, hs2⟩
      have b3 := h3 s ⟨hs, hs2⟩
      simp only [Real.norm_eq_abs, Pi.mul_apply, id_eq] at b1 b2 b3
      have := le_abs_self M1
      have := le_abs_self M2
      have := le_abs_self M3
      have := le_abs_self (smoothStepScaledDeriv s)
      refine ⟨by linarith, by linarith, by linarith⟩
    · simp only [smoothStepMulDeriv_of_two_lt hs2, smoothStepScaledDeriv_of_two_lt hs2, smoothStepMulDeriv_deriv_of_two_lt hs2, zero_mul, abs_zero,
        abs_one]
      refine ⟨by linarith, by linarith, by linarith⟩
variable {ρ : ℝ} {p : ℝ → ℝ}
theorem extendedCutoff_isRadialCutoff (hR : CutoffFactorIsRadialCutoff) (hρ : 0 < ρ) (hp : IsCutoff ρ p) :
    IsRadialCutoff ρ (extendedCutoff ρ p) := hR ρ p hρ hp
theorem extendedCutoff_contDiff (hR : CutoffFactorIsRadialCutoff) (hρ : 0 < ρ) (hp : IsCutoff ρ p) :
    ContDiff ℝ 1 (extendedCutoff ρ p) := (extendedCutoff_isRadialCutoff hR hρ hp).smooth
theorem extendedCutoff_eq_exp {u : ℝ} (h0 : 0 ≤ u) (h1 : u < ρ) : extendedCutoff ρ p u = Real.exp (- p u) := by
  simp [extendedCutoff, cutoffFactor, max_eq_left h0, h1]
theorem extendedCutoff_pos (hR : CutoffFactorIsRadialCutoff) (hρ : 0 < ρ) (hp : IsCutoff ρ p) {u : ℝ} (h0 : 0 ≤ u)
    (h1 : u < ρ) : 0 < extendedCutoff ρ p u := (extendedCutoff_isRadialCutoff hR hρ hp).pos u h0 h1
theorem extendedCutoff_eq_zero (hR : CutoffFactorIsRadialCutoff) (hρ : 0 < ρ) (hp : IsCutoff ρ p) {u : ℝ} (h1 : ρ ≤ u) :
    extendedCutoff ρ p u = 0 := (extendedCutoff_isRadialCutoff hR hρ hp).zero u h1
theorem extendedCutoff_nonneg (hR : CutoffFactorIsRadialCutoff) (hρ : 0 < ρ) (hp : IsCutoff ρ p) (u : ℝ) :
    0 ≤ extendedCutoff ρ p u := by
  simp only [extendedCutoff, cutoffFactor]
  split_ifs
  · exact (Real.exp_pos _).le
  · exact le_rfl
theorem extendedCutoff_inner (hρ : 0 < ρ) (hp : IsCutoff ρ p) {u : ℝ} (h1 : u < 5 * ρ / 8) :
    extendedCutoff ρ p u = 1 := by
  have e0 : 0 ≤ max u 0 := le_max_right _ _
  have e1 : max u 0 ≤ 5 * ρ / 8 := max_le h1.le (by positivity)
  have e2 : max u 0 < ρ := by linarith
  simp [extendedCutoff, cutoffFactor, e2, hp.vanish_small _ e0 e1]
theorem extendedCutoff_hasDerivAt (hρ : 0 < ρ) (hp : IsCutoff ρ p) {u : ℝ} (h1 : u < ρ) :
    HasDerivAt (extendedCutoff ρ p) (- cutoffSlope ρ p u * extendedCutoff ρ p u) u := by
  rcases lt_or_ge u (5 * ρ / 8) with h | h
  · have hev : extendedCutoff ρ p =ᶠ[nhds u] fun _ => 1 := by
      filter_upwards [Iio_mem_nhds h] with v hv
      exact extendedCutoff_inner hρ hp hv
    rw [cutoffSlope_inner hρ hp h]
    simpa using (hasDerivAt_const u (1 : ℝ)).congr_of_eventuallyEq hev
  · have hu : ρ / 2 < u := by linarith
    have hev : extendedCutoff ρ p =ᶠ[nhds u] fun v => Real.exp (- p v) := by
      filter_upwards [Ioo_mem_nhds hu h1] with v hv
      exact extendedCutoff_eq_exp (by linarith [hv.1]) hv.2
    rw [extendedCutoff_eq_exp (by linarith) h1, cutoffSlope_outer hρ hu]
    have h2 := ((cutoff_hasDerivAt hp (by linarith) h1).neg).exp
    refine (HasDerivAt.congr_deriv h2 ?_).congr_of_eventuallyEq hev
    simp only [Pi.neg_apply]
    ring
def levelStep (ρ : ℝ) (p : ℝ → ℝ) (ε u : ℝ) : ℝ := smoothStep (extendedCutoff ρ p u / ε)
def levelStepDeriv (ρ : ℝ) (p : ℝ → ℝ) (ε u : ℝ) : ℝ := - smoothStepScaledDeriv (extendedCutoff ρ p u / ε) * cutoffSlope ρ p u
def levelRatio (ρ : ℝ) (p : ℝ → ℝ) (ε u : ℝ) : ℝ := smoothStepMulDeriv (extendedCutoff ρ p u / ε) * cutoffSlope ρ p u / u
variable {ε : ℝ}
theorem levelStep_nonneg (u : ℝ) : 0 ≤ levelStep ρ p ε u := smoothStep_nonneg _
theorem levelStep_le_one (u : ℝ) : levelStep ρ p ε u ≤ 1 := smoothStep_le_one _
theorem levelStep_contDiff (hR : CutoffFactorIsRadialCutoff) (hρ : 0 < ρ) (hp : IsCutoff ρ p) :
    ContDiff ℝ 1 (levelStep ρ p ε) :=
  (smoothStep_contDiff.of_le (by simp)).comp ((extendedCutoff_contDiff hR hρ hp).div_const ε)
theorem eventually_extendedCutoff_div_lt_one (hR : CutoffFactorIsRadialCutoff) (hρ : 0 < ρ) (hp : IsCutoff ρ p) (hε : 0 < ε)
    {u : ℝ} (h1 : ρ ≤ u) : ∀ᶠ v in nhds u, extendedCutoff ρ p v / ε < 1 := by
  have hc : ContinuousAt (fun v => extendedCutoff ρ p v / ε) u :=
    ((extendedCutoff_contDiff hR hρ hp).continuous.div_const ε).continuousAt
  have h0 : extendedCutoff ρ p u / ε < 1 := by
    rw [extendedCutoff_eq_zero hR hρ hp h1]
    simp
  exact hc.eventually (Iio_mem_nhds h0)
theorem levelStep_hasDerivAt (hR : CutoffFactorIsRadialCutoff) (hρ : 0 < ρ) (hp : IsCutoff ρ p) (hε : 0 < ε) (u : ℝ) :
    HasDerivAt (levelStep ρ p ε) (levelStepDeriv ρ p ε u) u := by
  rcases lt_or_ge u ρ with h1 | h1
  · have h2 := extendedCutoff_hasDerivAt hρ hp h1
    have h3 : HasDerivAt smoothStep (deriv smoothStep (extendedCutoff ρ p u / ε)) (extendedCutoff ρ p u / ε) :=
      ((smoothStep_contDiff.differentiable (by simp)) _).hasDerivAt
    refine HasDerivAt.congr_deriv (h3.comp u (h2.div_const ε)) ?_
    simp only [levelStepDeriv, smoothStepScaledDeriv]
    ring
  · have hev : levelStep ρ p ε =ᶠ[nhds u] fun _ => 0 := by
      filter_upwards [eventually_extendedCutoff_div_lt_one hR hρ hp hε h1] with v hv
      exact smoothStep_of_le_one hv.le
    have e : levelStepDeriv ρ p ε u = 0 := by
      simp [levelStepDeriv, extendedCutoff_eq_zero hR hρ hp h1, smoothStepScaledDeriv]
    rw [e]
    exact (hasDerivAt_const u (0 : ℝ)).congr_of_eventuallyEq hev
theorem continuous_mul_comp_extendedCutoff (hR : CutoffFactorIsRadialCutoff) (hρ : 0 < ρ) (hp : IsCutoff ρ p) (hε : 0 < ε)
    {g f : ℝ → ℝ} (hf : Continuous f) (hf0 : ∀ s, s < 1 → f s = 0)
    (hg : ∀ u, u < ρ → ContinuousAt g u) :
    Continuous fun u => g u * f (extendedCutoff ρ p u / ε) := by
  rw [continuous_iff_continuousAt]
  intro u
  have hc : ContinuousAt (fun v => f (extendedCutoff ρ p v / ε)) u :=
    (hf.comp ((extendedCutoff_contDiff hR hρ hp).continuous.div_const ε)).continuousAt
  rcases lt_or_ge u ρ with h1 | h1
  · exact (hg u h1).mul hc
  · have hev : (fun u => g u * f (extendedCutoff ρ p u / ε)) =ᶠ[nhds u] fun _ => 0 := by
      filter_upwards [eventually_extendedCutoff_div_lt_one hR hρ hp hε h1] with v hv
      rw [hf0 _ hv, mul_zero]
    exact continuousAt_const.congr hev.symm
theorem contDiff_mul_comp_extendedCutoff (hR : CutoffFactorIsRadialCutoff) (hρ : 0 < ρ) (hp : IsCutoff ρ p) (hε : 0 < ε)
    {g f : ℝ → ℝ} (hf : ContDiff ℝ 1 f) (hf0 : ∀ s, s < 1 → f s = 0)
    (hg : ∀ u, u < ρ → ContDiffAt ℝ 1 g u) :
    ContDiff ℝ 1 fun u => g u * f (extendedCutoff ρ p u / ε) := by
  rw [contDiff_iff_contDiffAt]
  intro u
  have hc : ContDiffAt ℝ 1 (fun v => f (extendedCutoff ρ p v / ε)) u :=
    (hf.comp ((extendedCutoff_contDiff hR hρ hp).div_const ε)).contDiffAt
  rcases lt_or_ge u ρ with h1 | h1
  · exact (hg u h1).mul hc
  · have hev : (fun u => g u * f (extendedCutoff ρ p u / ε)) =ᶠ[nhds u] fun _ => 0 := by
      filter_upwards [eventually_extendedCutoff_div_lt_one hR hρ hp hε h1] with v hv
      rw [hf0 _ hv, mul_zero]
    exact contDiffAt_const.congr_of_eventuallyEq hev
theorem cutoffSlope_div_contDiffAt (hρ : 0 < ρ) (hp : IsCutoff ρ p) {u : ℝ} (h1 : u < ρ) :
    ContDiffAt ℝ 1 (fun v => cutoffSlope ρ p v / v) u := by
  rcases lt_or_ge u (5 * ρ / 8) with h | h
  · have hev : (fun v => cutoffSlope ρ p v / v) =ᶠ[nhds u] fun _ => 0 := by
      filter_upwards [Iio_mem_nhds h] with v hv
      rw [cutoffSlope_inner hρ hp hv, zero_div]
    exact contDiffAt_const.congr_of_eventuallyEq hev
  · have hu : u ≠ 0 := by
      have : 0 < u := by linarith
      exact this.ne'
    exact (cutoffSlope_contDiffAt hρ hp h1).div contDiffAt_id hu
end YangMills.Construction.ColdStepAtMirrorFrames.ThirdDerivative
end
noncomputable section
open MeasureTheory Set
namespace YangMills.Construction.ColdStepAtMirrorFrames.ThirdDerivative
variable {ι : Type} [Fintype ι] [DecidableEq ι]
theorem hasDerivAt_line_fderiv {G : BondField ι → ℝ} (hG : Differentiable ℝ G) (η u : BondField ι) :
    HasDerivAt (fun s : ℝ => G (η + s • u)) (fderiv ℝ G η u) 0 := by apply _root_.YangMills.Construction.ConvexBallLaws.SecondMoment.hasDerivAt_fderiv_line <;> assumption
def bondDilation (b : ι) (η : BondField ι) : BondField ι := Pi.single b (η b)
theorem integrable_mul_of_hasCompactSupport {ϱ g : BondField ι → ℝ} (hϱ : Continuous ϱ)
    (hc : HasCompactSupport ϱ) (hg : Continuous g) : Integrable (fun η => g η * ϱ η) := by apply _root_.YangMills.Construction.ConvexBallLaws.SecondMoment.integrable_mul_of_hasCompactSupport <;> assumption
theorem integral_mul_fderiv_dir {T ϱ : BondField ι → ℝ} (hT : ContDiff ℝ 1 T) (hϱ : ContDiff ℝ 1 ϱ)
    (hc : HasCompactSupport ϱ) (v : BondField ι) :
    ∫ η, T η * fderiv ℝ ϱ η v = - ∫ η, fderiv ℝ T η v * ϱ η := by
  have hT' : Differentiable ℝ T := hT.differentiable (by norm_num)
  have hϱ' : Differentiable ℝ ϱ := hϱ.differentiable (by norm_num)
  have hFT : Continuous (fderiv ℝ T) := hT.continuous_fderiv (by norm_num)
  have hFϱ : Continuous (fderiv ℝ ϱ) := hϱ.continuous_fderiv (by norm_num)
  have hvc : Continuous fun η => fderiv ℝ ϱ η v := hFϱ.clm_apply continuous_const
  have hFTv : Continuous fun η => fderiv ℝ T η v := hFT.clm_apply continuous_const
  have i1 : Integrable fun η => fderiv ℝ T η v * ϱ η := integrable_mul_of_hasCompactSupport hϱ.continuous hc hFTv
  have i2 : Integrable fun η => T η * fderiv ℝ ϱ η v :=
    Continuous.integrable_of_hasCompactSupport (hT.continuous.mul hvc)
      (hc.fderiv_apply (𝕜 := ℝ) v).mul_left
  have i3 : Integrable fun η => T η * ϱ η := integrable_mul_of_hasCompactSupport hϱ.continuous hc hT.continuous
  exact integral_mul_fderiv_eq_neg_fderiv_mul_of_integrable i1 i2 i3 (fun x _ => hT' x)
    (fun x _ => hϱ' x)
theorem integral_mul_fderiv_bondDilation {T ϱ : BondField ι → ℝ} (hT : ContDiff ℝ 1 T) (hϱ : ContDiff ℝ 1 ϱ)
    (hc : HasCompactSupport ϱ) (b : ι) :
    ∫ η, T η * fderiv ℝ ϱ η (bondDilation b η) =
      - ∫ η, (fderiv ℝ T η (bondDilation b η) + 3 * T η) * ϱ η := by apply _root_.YangMills.Construction.ConvexBallLaws.SecondMoment.integral_mul_fderiv_bondDilation <;> assumption
theorem radialFn_contDiff {f : ℝ → ℝ} (hf : ContDiff ℝ 1 f) {c : ℝ} (hc : 0 < c)
    (h0 : ∀ u, u < c → f u = 0) : ContDiff ℝ 1 (fun v : BondVector => f ‖v‖) := by
  rw [contDiff_iff_contDiffAt]
  intro v
  by_cases hv : v = 0
  · subst hv
    have : (fun v : BondVector => f ‖v‖) =ᶠ[nhds 0] fun _ => (0 : ℝ) := by
      have hb : Metric.ball (0 : BondVector) c ∈ nhds (0 : BondVector) :=
        Metric.ball_mem_nhds _ hc
      filter_upwards [hb] with w hw
      exact h0 _ (by simpa using hw)
    exact contDiffAt_const.congr_of_eventuallyEq this
  · exact hf.contDiffAt.comp v (contDiffAt_norm ℝ hv)
theorem radialFn_bond_contDiff {f : ℝ → ℝ} (hf : ContDiff ℝ 1 f) {c : ℝ} (hc : 0 < c)
    (h0 : ∀ u, u < c → f u = 0) (b : ι) : ContDiff ℝ 1 (fun η : BondField ι => f ‖η b‖) :=
  (radialFn_contDiff hf hc h0).comp (contDiff_apply ℝ BondVector b)
theorem norm_add_smul_bondDilation (η : BondField ι) (b : ι) (v : ℝ) (hv : v ∈ Ioo (-1 : ℝ) 1) :
    ‖(η + v • bondDilation b η) b‖ = (1 + v) * ‖η b‖ := by
  have e : (η + v • bondDilation b η) b = (1 + v) • η b := by
    simp [bondDilation, add_smul]
  rw [e, norm_smul, Real.norm_eq_abs, abs_of_pos (by linarith [hv.1])]
theorem radialFn_fderiv_bondDilation {f : ℝ → ℝ} (hf : ContDiff ℝ 1 f) {c : ℝ} (hc : 0 < c)
    (h0 : ∀ u, u < c → f u = 0) (b : ι) (η : BondField ι) :
    fderiv ℝ (fun ζ : BondField ι => f ‖ζ b‖) η (bondDilation b η) =
      deriv f ‖η b‖ * ‖η b‖ := by
  have hd : Differentiable ℝ (fun ζ : BondField ι => f ‖ζ b‖) :=
    (radialFn_bond_contDiff hf hc h0 b).differentiable (by norm_num)
  have hline := hasDerivAt_line_fderiv hd η (bondDilation b η)
  have hfd : HasDerivAt f (deriv f ‖η b‖) ((1 + 0) * ‖η b‖) := by
    simpa using ((hf.differentiable (by norm_num)) ‖η b‖).hasDerivAt
  have h1 : HasDerivAt (fun s : ℝ => (1 + s) * ‖η b‖) ‖η b‖ 0 := by
    have := ((hasDerivAt_id (0 : ℝ)).const_add 1).mul_const ‖η b‖
    simpa using this
  have h2 : HasDerivAt (fun s : ℝ => f ((1 + s) * ‖η b‖)) (deriv f ‖η b‖ * ‖η b‖) 0 :=
    hfd.comp (0 : ℝ) h1
  have heq : (fun s : ℝ => f ‖(η + s • bondDilation b η) b‖) =ᶠ[nhds 0]
      fun s : ℝ => f ((1 + s) * ‖η b‖) := by
    filter_upwards [Ioo_mem_nhds (by norm_num : (-1 : ℝ) < 0) (by norm_num : (0 : ℝ) < 1)] with v hv
    rw [norm_add_smul_bondDilation η b v hv]
  exact hline.unique (h2.congr_of_eventuallyEq heq)
variable {ρ : ℝ} {p : ℝ → ℝ} {Ψ : BondField ι → ℝ}
theorem radialWeightProd_fderiv_bondDilation (hρ : 0 < ρ) (hp : IsCutoff ρ p)
    (h : IsCutoffMeasureData ρ (extendedCutoff ρ p) Ψ) (η : BondField ι) (b : ι) (hu : ‖η b‖ < ρ) :
    fderiv ℝ (radialWeightProd (ι := ι) (extendedCutoff ρ p)) η (bondDilation b η) =
      - cutoffSlope ρ p ‖η b‖ * ‖η b‖ * radialWeightProd (extendedCutoff ρ p) η := by
  have hdiff : Differentiable ℝ (radialWeightProd (ι := ι) (extendedCutoff ρ p)) :=
    (radialWeightProd_contDiff h).differentiable (by norm_num)
  have hline := hasDerivAt_line_fderiv hdiff η (bondDilation b η)
  set c : ℝ := ∏ b' ∈ Finset.univ.erase b, extendedCutoff ρ p ‖η b'‖ with hc
  have hrd : HasDerivAt (extendedCutoff ρ p) (- cutoffSlope ρ p ‖η b‖ * extendedCutoff ρ p ‖η b‖)
      ((1 + 0) * ‖η b‖) := by
    simpa using extendedCutoff_hasDerivAt hρ hp hu
  have h1 : HasDerivAt (fun s : ℝ => (1 + s) * ‖η b‖) ‖η b‖ 0 := by
    have := ((hasDerivAt_id (0 : ℝ)).const_add 1).mul_const ‖η b‖
    simpa using this
  have h2 : HasDerivAt (fun s : ℝ => c * extendedCutoff ρ p ((1 + s) * ‖η b‖))
      (c * (- cutoffSlope ρ p ‖η b‖ * extendedCutoff ρ p ‖η b‖ * ‖η b‖)) 0 := by
    have h3 : HasDerivAt (fun s : ℝ => extendedCutoff ρ p ((1 + s) * ‖η b‖))
        (- cutoffSlope ρ p ‖η b‖ * extendedCutoff ρ p ‖η b‖ * ‖η b‖) 0 :=
      HasDerivAt.comp (h₂ := extendedCutoff ρ p) (h := fun s : ℝ => (1 + s) * ‖η b‖) (0 : ℝ) hrd h1
    exact h3.const_mul c
  have heq : (fun s : ℝ => radialWeightProd (extendedCutoff ρ p) (η + s • bondDilation b η)) =ᶠ[nhds 0]
      fun s : ℝ => c * extendedCutoff ρ p ((1 + s) * ‖η b‖) := by
    filter_upwards [Ioo_mem_nhds (by norm_num : (-1 : ℝ) < 0) (by norm_num : (0 : ℝ) < 1)] with s hs
    unfold radialWeightProd
    rw [← Finset.mul_prod_erase Finset.univ _ (Finset.mem_univ b), mul_comm]
    congr 1
    · apply Finset.prod_congr rfl
      intro b' hb'
      have hne : b' ≠ b := Finset.ne_of_mem_erase hb'
      simp [bondDilation, Pi.single_eq_of_ne hne]
    · rw [norm_add_smul_bondDilation η b s hs]
  have hu' := hline.unique (h2.congr_of_eventuallyEq heq)
  rw [hu']
  have e : radialWeightProd (extendedCutoff ρ p) η = c * extendedCutoff ρ p ‖η b‖ := by
    unfold radialWeightProd
    rw [← Finset.mul_prod_erase Finset.univ _ (Finset.mem_univ b), mul_comm]
  rw [e]
  ring
theorem ballDensity_fderiv (h : IsCutoffMeasureData ρ (extendedCutoff ρ p) Ψ) (η u : BondField ι) :
    fderiv ℝ (ballDensity (extendedCutoff ρ p) Ψ) η u =
      Real.exp (- Ψ η) * fderiv ℝ (radialWeightProd (extendedCutoff ρ p)) η u -
        ballDensity (extendedCutoff ρ p) Ψ η * fderiv ℝ Ψ η u := by
  have hR := ((radialWeightProd_contDiff (ι := ι) h).differentiable (by norm_num) η).hasFDerivAt
  have hΨ' := ((h.smooth.differentiable (by norm_num)) η).hasFDerivAt
  have hE := hΨ'.neg.exp
  have e : ballDensity (extendedCutoff ρ p) Ψ = fun y => radialWeightProd (extendedCutoff ρ p) y * Real.exp (- Ψ y) := rfl
  have h' : fderiv ℝ (fun y => radialWeightProd (extendedCutoff ρ p) y * Real.exp (- Ψ y)) η = _ :=
    (hR.mul hE).fderiv
  rw [e, h']
  simp only [_root_.add_apply, _root_.smul_apply, smul_eq_mul,
    _root_.neg_apply, Pi.neg_apply]
  ring
theorem ballDensity_fderiv_bondDilation (hρ : 0 < ρ) (hp : IsCutoff ρ p)
    (h : IsCutoffMeasureData ρ (extendedCutoff ρ p) Ψ) (η : BondField ι) (b : ι) (hu : ‖η b‖ < ρ) :
    fderiv ℝ (ballDensity (extendedCutoff ρ p) Ψ) η (bondDilation b η) =
      (- cutoffSlope ρ p ‖η b‖ * ‖η b‖ - fderiv ℝ Ψ η (bondDilation b η)) *
        ballDensity (extendedCutoff ρ p) Ψ η := by
  rw [ballDensity_fderiv h, radialWeightProd_fderiv_bondDilation hρ hp h η b hu]
  simp only [ballDensity]
  ring
theorem ballExpectation_radial_identity (hρ : 0 < ρ) (hp : IsCutoff ρ p) (h : IsCutoffMeasureData ρ (extendedCutoff ρ p) Ψ) (b : ι)
    {φ : ℝ → ℝ} (hφ : ContDiff ℝ 1 φ) (h0 : ∀ u, u < ρ / 4 → φ u = 0) (h1 : ∀ u, ρ ≤ u → φ u = 0)
    (hA : Continuous fun u => φ u * cutoffSlope ρ p u) :
    ballExpectation (extendedCutoff ρ p) Ψ (fun η => φ ‖η b‖ * cutoffSlope ρ p ‖η b‖) +
        ballExpectation (extendedCutoff ρ p) Ψ (fun η => φ ‖η b‖ / ‖η b‖ * fderiv ℝ Ψ η (bondDilation b η)) =
      ballExpectation (extendedCutoff ρ p) Ψ (fun η => deriv φ ‖η b‖ + 2 * (φ ‖η b‖ / ‖η b‖)) := by
  have hρ4 : 0 < ρ / 4 := by positivity
  set f : ℝ → ℝ := fun u => φ u / u with hfdef
  have hf0 : ∀ u, u < ρ / 4 → f u = 0 := fun u hu => by simp [hfdef, h0 u hu]
  have hf : ContDiff ℝ 1 f := by
    rw [contDiff_iff_contDiffAt]
    intro u
    rcases lt_or_ge u (ρ / 4) with hu | hu
    · have hev : f =ᶠ[nhds u] fun _ => 0 := by
        filter_upwards [Iio_mem_nhds hu] with v hv
        exact hf0 v hv
      exact contDiffAt_const.congr_of_eventuallyEq hev
    · exact hφ.contDiffAt.div contDiffAt_id (by
        have : 0 < u := by linarith
        exact this.ne')
  have hT : ContDiff ℝ 1 (fun η : BondField ι => f ‖η b‖) := radialFn_bond_contDiff hf hρ4 hf0 b
  have hblock := integral_mul_fderiv_bondDilation hT (ballDensity_contDiff h) (ballDensity_hasCompactSupport h) b
  have hdf : ∀ u : ℝ, 0 ≤ u → deriv f u * u + 3 * f u = deriv φ u + 2 * (φ u / u) := by
    intro u hu
    rcases lt_or_ge u (ρ / 4) with hu4 | hu4
    · have e1 : deriv f u = 0 := by
        have hev : f =ᶠ[nhds u] fun _ => 0 := by
          filter_upwards [Iio_mem_nhds hu4] with v hv
          exact hf0 v hv
        rw [hev.deriv_eq]
        simp
      have e2 : deriv φ u = 0 := by
        have hev : φ =ᶠ[nhds u] fun _ => 0 := by
          filter_upwards [Iio_mem_nhds hu4] with v hv
          exact h0 v hv
        rw [hev.deriv_eq]
        simp
      simp [e1, e2, hf0 u hu4, h0 u hu4]
    · have hu0 : u ≠ 0 := by
        have : 0 < u := by linarith
        exact this.ne'
      have hd : HasDerivAt φ (deriv φ u) u := ((hφ.differentiable (by norm_num)) u).hasDerivAt
      have e1 : deriv f u = (deriv φ u * u - φ u * 1) / u ^ 2 := (hd.div (hasDerivAt_id u) hu0).deriv
      rw [e1]
      simp only [hfdef]
      field_simp
      ring
  have hL : ∀ η : BondField ι, f ‖η b‖ * fderiv ℝ (ballDensity (extendedCutoff ρ p) Ψ) η (bondDilation b η) =
      - ((φ ‖η b‖ * cutoffSlope ρ p ‖η b‖ + φ ‖η b‖ / ‖η b‖ * fderiv ℝ Ψ η (bondDilation b η)) *
        ballDensity (extendedCutoff ρ p) Ψ η) := by
    intro η
    rcases lt_or_ge ‖η b‖ ρ with hu | hu
    · rw [ballDensity_fderiv_bondDilation hρ hp h η b hu]
      simp only [hfdef]
      by_cases h00 : ‖η b‖ = 0
      · rw [h00, h0 0 (by positivity)]
        simp
      · field_simp
        ring
    · simp [hfdef, h1 _ hu]
  have hR : ∀ η : BondField ι,
      (fderiv ℝ (fun ζ : BondField ι => f ‖ζ b‖) η (bondDilation b η) + 3 * f ‖η b‖) *
        ballDensity (extendedCutoff ρ p) Ψ η =
      (deriv φ ‖η b‖ + 2 * (φ ‖η b‖ / ‖η b‖)) * ballDensity (extendedCutoff ρ p) Ψ η := by
    intro η
    rw [radialFn_fderiv_bondDilation hf hρ4 hf0 b η, hdf _ (norm_nonneg _)]
  simp only [hL, hR, integral_neg, neg_inj] at hblock
  have c1 : Continuous fun η : BondField ι => φ ‖η b‖ * cutoffSlope ρ p ‖η b‖ :=
    hA.comp ((continuous_apply b).norm)
  have hdilc : Continuous (bondDilation (ι := ι) b) := by
    unfold bondDilation
    exact (ContinuousLinearMap.single ℝ (fun _ : ι => BondVector) b).continuous.comp (continuous_apply b)
  have c2 : Continuous fun η : BondField ι => φ ‖η b‖ / ‖η b‖ * fderiv ℝ Ψ η (bondDilation b η) := by
    refine (hT.continuous).mul ?_
    exact ((h.smooth.continuous_fderiv (by norm_num))).clm_apply hdilc
  rw [← ballExpectation_add h c1 c2]
  simp only [ballExpectation_def]
  congr 1
end YangMills.Construction.ColdStepAtMirrorFrames.ThirdDerivative
end
noncomputable section
open MeasureTheory Set
namespace YangMills.Construction.ColdStepAtMirrorFrames.ThirdDerivative
variable {ι : Type} [Fintype ι] [DecidableEq ι]
variable {ρ : ℝ} {p : ℝ → ℝ} {Ψ : BondField ι → ℝ}
def outerStep (ρ u : ℝ) : ℝ := Real.smoothTransition (16 * u / ρ - 8)
theorem outerStep_contDiff (ρ : ℝ) : ContDiff ℝ smoothOrder (outerStep ρ) :=
  Real.smoothTransition.contDiff.comp (((contDiff_const.mul contDiff_id).div_const ρ).sub contDiff_const)
theorem outerStep_of_le (hρ : 0 < ρ) {u : ℝ} (h : u ≤ ρ / 2) : outerStep ρ u = 0 := by
  apply Real.smoothTransition.zero_of_nonpos
  have : 16 * u / ρ ≤ 8 := by
    rw [div_le_iff₀ hρ]
    linarith
  linarith
theorem outerStep_of_ge (hρ : 0 < ρ) {u : ℝ} (h : 9 * ρ / 16 ≤ u) : outerStep ρ u = 1 := by
  apply Real.smoothTransition.one_of_one_le
  have : 9 ≤ 16 * u / ρ := by
    rw [le_div_iff₀ hρ]
    linarith
  linarith
theorem outerStep_nonneg (u : ℝ) : 0 ≤ outerStep ρ u := Real.smoothTransition.nonneg _
theorem outerStep_le_one (u : ℝ) : outerStep ρ u ≤ 1 := Real.smoothTransition.le_one _
theorem outerStep_deriv_of_gt (hρ : 0 < ρ) {u : ℝ} (h : 9 * ρ / 16 < u) : deriv (outerStep ρ) u = 0 := by
  have hev : outerStep ρ =ᶠ[nhds u] fun _ => 1 := by
    filter_upwards [Ioi_mem_nhds h] with v hv
    exact outerStep_of_ge hρ (le_of_lt hv)
  rw [hev.deriv_eq]
  simp
theorem outerStep_deriv_of_lt (hρ : 0 < ρ) {u : ℝ} (h : u < ρ / 2) : deriv (outerStep ρ) u = 0 := by
  have hev : outerStep ρ =ᶠ[nhds u] fun _ => 0 := by
    filter_upwards [Iio_mem_nhds h] with v hv
    exact outerStep_of_le hρ (le_of_lt hv)
  rw [hev.deriv_eq]
  simp
theorem outerStep_deriv_bounded (hρ : 0 < ρ) : ∃ c : ℝ, 0 ≤ c ∧ ∀ u, |deriv (outerStep ρ) u| ≤ c := by
  have hc : IsCompact (Icc (ρ / 2) (9 * ρ / 16)) := isCompact_Icc
  have hcont : Continuous (deriv (outerStep ρ)) := (outerStep_contDiff ρ).continuous_deriv (by simp)
  obtain ⟨M, hM⟩ := hc.exists_bound_of_continuousOn hcont.continuousOn
  refine ⟨|M|, abs_nonneg _, fun u => ?_⟩
  rcases lt_or_ge u (ρ / 2) with h1 | h1
  · rw [outerStep_deriv_of_lt hρ h1]
    simpa using abs_nonneg M
  · rcases lt_or_ge (9 * ρ / 16) u with h2 | h2
    · rw [outerStep_deriv_of_gt hρ h2]
      simpa using abs_nonneg M
    · exact (hM u ⟨h1, h2⟩).trans (le_abs_self M)
structure SlopeMomentHyp (ρ : ℝ) (p : ℝ → ℝ) (Ψ : BondField ι → ℝ) (b : ι) (B : ℝ)
    (β : BondField ι → ℝ) : Prop where
  pos : 0 < ρ
  cutoff : IsCutoff ρ p
  data : IsCutoffMeasureData ρ (extendedCutoff ρ p) Ψ
  one_le : 1 ≤ B
  slope_le : ∀ η, InOpenBalls ρ η → |fderiv ℝ Ψ η (bondDilation b η)| ≤ B * ‖η b‖
  weight_cont : Continuous β
  weight_nonneg : ∀ η, InOpenBalls ρ η → 0 ≤ β η
  weight_ge_one : ∀ η, InOpenBalls ρ η → ρ / 2 ≤ ‖η b‖ → 1 ≤ β η
variable {b : ι} {B : ℝ} {β : BondField ι → ℝ}
theorem ballExpectation_radial_le (h : SlopeMomentHyp ρ p Ψ b B β) {φ : ℝ → ℝ} (hφ : ContDiff ℝ 1 φ)
    (h1 : ∀ u, ρ ≤ u → φ u = 0) (hA : Continuous fun u => φ u * cutoffSlope ρ p u)
    (hφ0 : ∀ u, 0 ≤ u → u < ρ → 0 ≤ φ u) (hs : ∀ u, u < ρ / 2 → φ u = 0) :
    ballExpectation (extendedCutoff ρ p) Ψ (fun η => φ ‖η b‖ * cutoffSlope ρ p ‖η b‖) ≤
      ballExpectation (extendedCutoff ρ p) Ψ (fun η => deriv φ ‖η b‖) +
        (4 / ρ + B) * ballExpectation (extendedCutoff ρ p) Ψ (fun η => φ ‖η b‖) := by
  have hρ := h.pos
  have hd := h.data
  have hid := ballExpectation_radial_identity hρ h.cutoff hd b hφ (fun u hu => hs u (by linarith)) h1 hA
  have hn : Continuous fun η : BondField ι => ‖η b‖ := (continuous_apply b).norm
  have hdil : Continuous (bondDilation (ι := ι) b) := by
    unfold bondDilation
    exact (ContinuousLinearMap.single ℝ (fun _ : ι => BondVector) b).continuous.comp (continuous_apply b)
  have hfr : ContDiff ℝ 1 (fun u => φ u / u) := by
    rw [contDiff_iff_contDiffAt]
    intro u
    rcases lt_or_ge u (ρ / 2) with hu | hu
    · have hev : (fun u => φ u / u) =ᶠ[nhds u] fun _ => 0 := by
        filter_upwards [Iio_mem_nhds hu] with v hv
        rw [hs v hv, zero_div]
      exact contDiffAt_const.congr_of_eventuallyEq hev
    · exact hφ.contDiffAt.div contDiffAt_id (by
        have : 0 < u := by linarith
        exact this.ne')
  have c1 : Continuous fun η : BondField ι => φ ‖η b‖ / ‖η b‖ := hfr.continuous.comp hn
  have c2 : Continuous fun η : BondField ι => fderiv ℝ Ψ η (bondDilation b η) :=
    (hd.smooth.continuous_fderiv (by norm_num)).clm_apply hdil
  have hle : ballExpectation (extendedCutoff ρ p) Ψ (fun η => deriv φ ‖η b‖ + 2 * (φ ‖η b‖ / ‖η b‖) -
        φ ‖η b‖ / ‖η b‖ * fderiv ℝ Ψ η (bondDilation b η)) ≤
      ballExpectation (extendedCutoff ρ p) Ψ (fun η => deriv φ ‖η b‖ + (4 / ρ + B) * φ ‖η b‖) := by
    apply ballExpectation_mono hd (by fun_prop) (by fun_prop)
    intro η hη
    have hu := norm_nonneg (η b)
    rcases lt_or_ge ‖η b‖ (ρ / 2) with h2 | h2
    · simp [hs _ h2]
    · have hu0 : 0 < ‖η b‖ := by linarith
      have hφe := hφ0 _ hu (hη b)
      have hsl := h.slope_le η hη
      have e1 : 2 * (φ ‖η b‖ / ‖η b‖) ≤ 4 / ρ * φ ‖η b‖ := by
        rw [div_mul_eq_mul_div, mul_div_assoc', div_le_div_iff₀ hu0 hρ]
        nlinarith
      have e2 : - (φ ‖η b‖ / ‖η b‖ * fderiv ℝ Ψ η (bondDilation b η)) ≤ B * φ ‖η b‖ := by
        have : |φ ‖η b‖ / ‖η b‖ * fderiv ℝ Ψ η (bondDilation b η)| ≤ B * φ ‖η b‖ := by
          rw [abs_mul, abs_of_nonneg (div_nonneg hφe hu)]
          calc φ ‖η b‖ / ‖η b‖ * |fderiv ℝ Ψ η (bondDilation b η)|
              ≤ φ ‖η b‖ / ‖η b‖ * (B * ‖η b‖) :=
                mul_le_mul_of_nonneg_left hsl (div_nonneg hφe hu)
            _ = B * φ ‖η b‖ := by
                field_simp
        linarith [neg_abs_le (φ ‖η b‖ / ‖η b‖ * fderiv ℝ Ψ η (bondDilation b η))]
      nlinarith
  have e1 : ballExpectation (extendedCutoff ρ p) Ψ (fun η => deriv φ ‖η b‖ + 2 * (φ ‖η b‖ / ‖η b‖) -
        φ ‖η b‖ / ‖η b‖ * fderiv ℝ Ψ η (bondDilation b η)) =
      ballExpectation (extendedCutoff ρ p) Ψ (fun η => φ ‖η b‖ * cutoffSlope ρ p ‖η b‖) := by
    rw [ballExpectation_sub hd (f := fun η => deriv φ ‖η b‖ + 2 * (φ ‖η b‖ / ‖η b‖))
      (g := fun η => φ ‖η b‖ / ‖η b‖ * fderiv ℝ Ψ η (bondDilation b η)) (by fun_prop) (by fun_prop)]
    linarith
  have e2 : ballExpectation (extendedCutoff ρ p) Ψ (fun η => deriv φ ‖η b‖ + (4 / ρ + B) * φ ‖η b‖) =
      ballExpectation (extendedCutoff ρ p) Ψ (fun η => deriv φ ‖η b‖) +
        (4 / ρ + B) * ballExpectation (extendedCutoff ρ p) Ψ (fun η => φ ‖η b‖) := by
    rw [ballExpectation_add hd (f := fun η => deriv φ ‖η b‖) (g := fun η => (4 / ρ + B) * φ ‖η b‖)
      (by fun_prop) (by fun_prop), ballExpectation_const_mul]
  rw [e1, e2] at hle
  exact hle
variable {ε : ℝ}
def slopePower (ρ : ℝ) (p : ℝ → ℝ) (ε : ℝ) (j : ℕ) (u : ℝ) : ℝ :=
  outerStep ρ u * cutoffSlope ρ p u ^ j * levelStep ρ p ε u
theorem slopePower_eq (ρ : ℝ) (p : ℝ → ℝ) (ε : ℝ) (j : ℕ) :
    slopePower ρ p ε j = fun u => (outerStep ρ u * cutoffSlope ρ p u ^ j) * smoothStep (extendedCutoff ρ p u / ε) := rfl
theorem slopePower_continuous (hR : CutoffFactorIsRadialCutoff) (hρ : 0 < ρ) (hp : IsCutoff ρ p) (hε : 0 < ε)
    (j : ℕ) : Continuous (slopePower ρ p ε j) := by
  rw [slopePower_eq]
  refine continuous_mul_comp_extendedCutoff hR hρ hp hε smoothStep_contDiff.continuous
    (fun s hs => smoothStep_of_le_one hs.le) fun u hu => ?_
  exact ((outerStep_contDiff ρ).continuous.continuousAt).mul
    (((cutoffSlope_hasDerivAt hρ hp hu).continuousAt).pow j)
theorem slopePower_contDiff (hR : CutoffFactorIsRadialCutoff) (hρ : 0 < ρ) (hp : IsCutoff ρ p) (hε : 0 < ε)
    (j : ℕ) : ContDiff ℝ 1 (slopePower ρ p ε j) := by
  rw [slopePower_eq]
  refine contDiff_mul_comp_extendedCutoff hR hρ hp hε (smoothStep_contDiff.of_le (by simp))
    (fun s hs => smoothStep_of_le_one hs.le) fun u hu => ?_
  exact ((outerStep_contDiff ρ).of_le (by simp)).contDiffAt.mul ((cutoffSlope_contDiffAt hρ hp hu).pow j)
theorem levelStep_eq_zero (hR : CutoffFactorIsRadialCutoff) (hρ : 0 < ρ) (hp : IsCutoff ρ p) (hε : 0 < ε) {u : ℝ}
    (h : ρ ≤ u) : levelStep ρ p ε u = 0 := by
  simp [levelStep, extendedCutoff_eq_zero hR hρ hp h, smoothStep_of_le_one]
theorem slopePower_of_ge (hR : CutoffFactorIsRadialCutoff) (hρ : 0 < ρ) (hp : IsCutoff ρ p) (hε : 0 < ε) (j : ℕ)
    {u : ℝ} (h : ρ ≤ u) : slopePower ρ p ε j u = 0 := by
  simp [slopePower, levelStep_eq_zero hR hρ hp hε h]
theorem slopePower_of_lt (hρ : 0 < ρ) (j : ℕ) {u : ℝ} (h : u < ρ / 2) : slopePower ρ p ε j u = 0 := by
  simp [slopePower, outerStep_of_le hρ h.le]
theorem slopePower_nonneg (hρ : 0 < ρ) (hp : IsCutoff ρ p) (j : ℕ) {u : ℝ} (h : u < ρ) :
    0 ≤ slopePower ρ p ε j u :=
  mul_nonneg (mul_nonneg (outerStep_nonneg _) (pow_nonneg (cutoffSlope_nonneg hρ hp h) j)) (levelStep_nonneg _)
theorem slopePower_mul_cutoffSlope (ρ : ℝ) (p : ℝ → ℝ) (ε : ℝ) (j : ℕ) (u : ℝ) :
    slopePower ρ p ε j u * cutoffSlope ρ p u = slopePower ρ p ε (j + 1) u := by
  simp only [slopePower, pow_succ]
  ring
theorem slopePower_hasDerivAt (hR : CutoffFactorIsRadialCutoff) (hρ : 0 < ρ) (hp : IsCutoff ρ p) (hε : 0 < ε) (j : ℕ)
    {u : ℝ} (hu : u < ρ) :
    HasDerivAt (slopePower ρ p ε j)
      ((deriv (outerStep ρ) u * cutoffSlope ρ p u ^ j +
          outerStep ρ u * ((j : ℝ) * cutoffSlope ρ p u ^ (j - 1) * cutoffCurvature ρ p u)) * levelStep ρ p ε u +
        outerStep ρ u * cutoffSlope ρ p u ^ j * levelStepDeriv ρ p ε u) u := by
  have h1 : HasDerivAt (outerStep ρ) (deriv (outerStep ρ) u) u :=
    (((outerStep_contDiff ρ).differentiable (by simp)) u).hasDerivAt
  have h2 := (cutoffSlope_hasDerivAt hρ hp hu).fun_pow j
  have h3 := levelStep_hasDerivAt hR hρ hp hε u
  exact (h1.mul h2).mul h3
theorem levelStepDeriv_nonpos (hR : CutoffFactorIsRadialCutoff) (hρ : 0 < ρ) (hp : IsCutoff ρ p) (hε : 0 < ε) {u : ℝ}
    (hu : u < ρ) : levelStepDeriv ρ p ε u ≤ 0 := by
  have h1 : 0 ≤ smoothStepScaledDeriv (extendedCutoff ρ p u / ε) :=
    smoothStepScaledDeriv_nonneg (div_nonneg (extendedCutoff_nonneg hR hρ hp u) hε.le)
  have h2 := cutoffSlope_nonneg hρ hp hu
  simp only [levelStepDeriv]
  nlinarith [mul_nonneg h1 h2]
def slopeMoment (ρ : ℝ) (p : ℝ → ℝ) (Ψ : BondField ι → ℝ) (b : ι) (ε : ℝ) (j : ℕ) : ℝ :=
  ballExpectation (extendedCutoff ρ p) Ψ (fun η => slopePower ρ p ε j ‖η b‖)
theorem slopeMoment_succ_le (hR : CutoffFactorIsRadialCutoff) (h : SlopeMomentHyp ρ p Ψ b B β) (hε : 0 < ε) (j : ℕ) :
    slopeMoment ρ p Ψ b ε (j + 1) ≤
      ballExpectation (extendedCutoff ρ p) Ψ (fun η => deriv (slopePower ρ p ε j) ‖η b‖) +
        (4 / ρ + B) * slopeMoment ρ p Ψ b ε j := by
  have hρ := h.pos
  have hp := h.cutoff
  have := ballExpectation_radial_le h (slopePower_contDiff hR hρ hp hε j) (fun u hu => slopePower_of_ge hR hρ hp hε j hu)
    (by
      have e : (fun u => slopePower ρ p ε j u * cutoffSlope ρ p u) = slopePower ρ p ε (j + 1) := by
        funext u
        exact slopePower_mul_cutoffSlope ρ p ε j u
      rw [e]
      exact slopePower_continuous hR hρ hp hε _)
    (fun u _ hu => slopePower_nonneg hρ hp j hu) (fun u hu => slopePower_of_lt hρ j hu)
  simpa only [slopeMoment, slopePower_mul_cutoffSlope] using this
theorem slopeMoment_zero_le (hR : CutoffFactorIsRadialCutoff) (h : SlopeMomentHyp ρ p Ψ b B β) (hε : 0 < ε) :
    slopeMoment ρ p Ψ b ε 0 ≤ ballExpectation (extendedCutoff ρ p) Ψ β := by
  have hρ := h.pos
  have hp := h.cutoff
  apply ballExpectation_mono h.data ((slopePower_continuous hR hρ hp hε 0).comp (continuous_apply b).norm) h.weight_cont
  intro η hη
  show slopePower ρ p ε 0 ‖η b‖ ≤ β η
  rcases lt_or_ge ‖η b‖ (ρ / 2) with h2 | h2
  · rw [slopePower_of_lt hρ 0 h2]
    exact h.weight_nonneg η hη
  · have h1 := h.weight_ge_one η hη h2
    have : slopePower ρ p ε 0 ‖η b‖ ≤ 1 := by
      simp only [slopePower, pow_zero, mul_one]
      nlinarith [outerStep_nonneg (ρ := ρ) ‖η b‖, outerStep_le_one (ρ := ρ) ‖η b‖,
        levelStep_nonneg (ρ := ρ) (p := p) (ε := ε) ‖η b‖, levelStep_le_one (ρ := ρ) (p := p) (ε := ε) ‖η b‖]
    linarith
theorem slopeMoment_one_le (hR : CutoffFactorIsRadialCutoff) (h : SlopeMomentHyp ρ p Ψ b B β) (hε : 0 < ε) {c : ℝ}
    (hc : ∀ u, |deriv (outerStep ρ) u| ≤ c) :
    slopeMoment ρ p Ψ b ε 1 ≤ (c + 4 / ρ + B) * ballExpectation (extendedCutoff ρ p) Ψ β := by
  have hρ := h.pos
  have hp := h.cutoff
  have hd := h.data
  have h1 := slopeMoment_succ_le hR h hε 0
  have h0 := slopeMoment_zero_le hR h hε
  have hc0 : 0 ≤ c := (abs_nonneg _).trans (hc 0)
  have hn : Continuous fun η : BondField ι => ‖η b‖ := (continuous_apply b).norm
  have h2 : ballExpectation (extendedCutoff ρ p) Ψ (fun η => deriv (slopePower ρ p ε 0) ‖η b‖) ≤
      ballExpectation (extendedCutoff ρ p) Ψ (fun η => c * β η) := by
    apply ballExpectation_mono hd (((slopePower_contDiff hR hρ hp hε 0).continuous_deriv (by norm_num)).comp hn)
      (continuous_const.mul h.weight_cont)
    intro η hη
    have hu := hη b
    show deriv (slopePower ρ p ε 0) ‖η b‖ ≤ c * β η
    rw [(slopePower_hasDerivAt hR hρ hp hε 0 hu).deriv]
    simp only [pow_zero, mul_one, Nat.cast_zero, zero_mul, mul_zero, add_zero]
    have t0 := levelStep_nonneg (ρ := ρ) (p := p) (ε := ε) ‖η b‖
    have t1 := levelStep_le_one (ρ := ρ) (p := p) (ε := ε) ‖η b‖
    have t2 := levelStepDeriv_nonpos hR hρ hp hε hu
    have p0 := outerStep_nonneg (ρ := ρ) ‖η b‖
    have e1 : outerStep ρ ‖η b‖ * levelStepDeriv ρ p ε ‖η b‖ ≤ 0 := mul_nonpos_of_nonneg_of_nonpos p0 t2
    rcases lt_or_ge ‖η b‖ (ρ / 2) with h3 | h3
    · rw [outerStep_deriv_of_lt hρ h3]
      have := mul_nonneg hc0 (h.weight_nonneg η hη)
      linarith
    · have h4 := h.weight_ge_one η hη h3
      have h5 := (abs_le.mp (hc ‖η b‖)).2
      have h6 : deriv (outerStep ρ) ‖η b‖ * levelStep ρ p ε ‖η b‖ ≤ c := by
        rcases le_or_gt 0 (deriv (outerStep ρ) ‖η b‖) with h7 | h7
        · nlinarith
        · nlinarith
      nlinarith
  rw [ballExpectation_const_mul] at h2
  have hpos : 0 ≤ 4 / ρ + B := by
    have := h.one_le
    positivity
  have := mul_le_mul_of_nonneg_left h0 hpos
  nlinarith
theorem slopeMoment_add_two_le (hR : CutoffFactorIsRadialCutoff) (h : SlopeMomentHyp ρ p Ψ b B β) (hε : 0 < ε) {j : ℕ}
    {C : ℝ} (hC0 : 0 ≤ C)
    (hC : ∀ u, u < ρ → cutoffCurvature ρ p u ≤ (1 / (2 * ((j : ℝ) + 1))) * cutoffSlope ρ p u ^ 2 + C) :
    slopeMoment ρ p Ψ b ε (j + 2) ≤
      2 * ((j : ℝ) + 1) * C * slopeMoment ρ p Ψ b ε j + 2 * (4 / ρ + B) * slopeMoment ρ p Ψ b ε (j + 1) := by
  have hρ := h.pos
  have hp := h.cutoff
  have hd := h.data
  have h1 := slopeMoment_succ_le hR h hε (j + 1)
  have hn : Continuous fun η : BondField ι => ‖η b‖ := (continuous_apply b).norm
  have cP : ∀ i, Continuous fun η : BondField ι => slopePower ρ p ε i ‖η b‖ := fun i =>
    (slopePower_continuous hR hρ hp hε i).comp hn
  have h2 : ballExpectation (extendedCutoff ρ p) Ψ (fun η => deriv (slopePower ρ p ε (j + 1)) ‖η b‖) ≤
      ballExpectation (extendedCutoff ρ p) Ψ (fun η => (1 / 2) * slopePower ρ p ε (j + 2) ‖η b‖ +
        (((j : ℝ) + 1) * C) * slopePower ρ p ε j ‖η b‖) := by
    apply ballExpectation_mono hd (((slopePower_contDiff hR hρ hp hε _).continuous_deriv (by norm_num)).comp hn)
      ((continuous_const.mul (cP _)).add (continuous_const.mul (cP _)))
    intro η hη
    have hu := hη b
    show deriv (slopePower ρ p ε (j + 1)) ‖η b‖ ≤
      (1 / 2) * slopePower ρ p ε (j + 2) ‖η b‖ + (((j : ℝ) + 1) * C) * slopePower ρ p ε j ‖η b‖
    rw [(slopePower_hasDerivAt hR hρ hp hε (j + 1) hu).deriv]
    set u := ‖η b‖ with hudef
    have t0 := levelStep_nonneg (ρ := ρ) (p := p) (ε := ε) u
    have t2 := levelStepDeriv_nonpos hR hρ hp hε hu
    have p0 := outerStep_nonneg (ρ := ρ) u
    have s0 := cutoffSlope_nonneg hρ hp hu
    have q0 := cutoffCurvature_nonneg hρ hp hu
    have z : deriv (outerStep ρ) u * cutoffSlope ρ p u ^ (j + 1) = 0 := by
      rcases lt_or_ge u (5 * ρ / 8) with h3 | h3
      · rw [cutoffSlope_inner hρ hp h3]
        simp
      · rw [outerStep_deriv_of_gt hρ (by linarith)]
        simp
    rw [z, zero_add]
    have e1 : outerStep ρ u * cutoffSlope ρ p u ^ (j + 1) * levelStepDeriv ρ p ε u ≤ 0 :=
      mul_nonpos_of_nonneg_of_nonpos (mul_nonneg p0 (pow_nonneg s0 _)) t2
    have hj : (0 : ℝ) < (j : ℝ) + 1 := by positivity
    have key : ((j + 1 : ℕ) : ℝ) * cutoffCurvature ρ p u ≤ (1 / 2) * cutoffSlope ρ p u ^ 2 + ((j : ℝ) + 1) * C := by
      have := mul_le_mul_of_nonneg_left (hC u hu) hj.le
      push_cast
      have e : ((j : ℝ) + 1) * (1 / (2 * ((j : ℝ) + 1)) * cutoffSlope ρ p u ^ 2 + C) =
          (1 / 2) * cutoffSlope ρ p u ^ 2 + ((j : ℝ) + 1) * C := by
        field_simp
      linarith
    have hw : 0 ≤ outerStep ρ u * cutoffSlope ρ p u ^ j * levelStep ρ p ε u :=
      mul_nonneg (mul_nonneg p0 (pow_nonneg s0 _)) t0
    have main2 := mul_le_mul_of_nonneg_left key hw
    simp only [slopePower, Nat.add_sub_cancel]
    have e2 : outerStep ρ u * (((j + 1 : ℕ) : ℝ) * cutoffSlope ρ p u ^ j * cutoffCurvature ρ p u) * levelStep ρ p ε u =
        outerStep ρ u * cutoffSlope ρ p u ^ j * levelStep ρ p ε u * (((j + 1 : ℕ) : ℝ) * cutoffCurvature ρ p u) := by
      ring
    have e3 : outerStep ρ u * cutoffSlope ρ p u ^ j * levelStep ρ p ε u * (1 / 2 * cutoffSlope ρ p u ^ 2 + ((j : ℝ) + 1) * C) =
        1 / 2 * (outerStep ρ u * cutoffSlope ρ p u ^ (j + 2) * levelStep ρ p ε u) +
          ((j : ℝ) + 1) * C * (outerStep ρ u * cutoffSlope ρ p u ^ j * levelStep ρ p ε u) := by
      rw [pow_add]
      ring
    rw [e2]
    linarith
  rw [ballExpectation_add hd (f := fun η => (1 / 2) * slopePower ρ p ε (j + 2) ‖η b‖)
    (g := fun η => (((j : ℝ) + 1) * C) * slopePower ρ p ε j ‖η b‖)
    (continuous_const.mul (cP _)) (continuous_const.mul (cP _)), ballExpectation_const_mul, ballExpectation_const_mul] at h2
  simp only [slopeMoment] at h1 ⊢
  nlinarith
theorem slopeMoment_le (hR : CutoffFactorIsRadialCutoff) (hρ : 0 < ρ) (hp : IsCutoff ρ p) (j : ℕ) :
    ∃ c : ℝ, 0 ≤ c ∧ ∀ (ι : Type) [Fintype ι] [DecidableEq ι] (Ψ : BondField ι → ℝ) (b : ι)
      (B : ℝ) (β : BondField ι → ℝ) (ε : ℝ), SlopeMomentHyp ρ p Ψ b B β → 0 < ε →
        slopeMoment ρ p Ψ b ε j ≤ c * B ^ j * ballExpectation (extendedCutoff ρ p) Ψ β := by
  obtain ⟨c₁, hc₁0, hc₁⟩ := outerStep_deriv_bounded hρ
  have two : ∀ j : ℕ, (∃ c : ℝ, 0 ≤ c ∧ ∀ (ι : Type) [Fintype ι] [DecidableEq ι]
      (Ψ : BondField ι → ℝ) (b : ι) (B : ℝ) (β : BondField ι → ℝ) (ε : ℝ),
      SlopeMomentHyp ρ p Ψ b B β → 0 < ε → slopeMoment ρ p Ψ b ε j ≤ c * B ^ j * ballExpectation (extendedCutoff ρ p) Ψ β) ∧
      (∃ c : ℝ, 0 ≤ c ∧ ∀ (ι : Type) [Fintype ι] [DecidableEq ι]
      (Ψ : BondField ι → ℝ) (b : ι) (B : ℝ) (β : BondField ι → ℝ) (ε : ℝ),
      SlopeMomentHyp ρ p Ψ b B β → 0 < ε →
        slopeMoment ρ p Ψ b ε (j + 1) ≤ c * B ^ (j + 1) * ballExpectation (extendedCutoff ρ p) Ψ β) := by
    intro j
    induction j with
    | zero =>
      refine ⟨⟨1, zero_le_one, ?_⟩, ⟨c₁ + 4 / ρ + 1, by positivity, ?_⟩⟩
      · intro ι _ _ Ψ b B β ε h hε
        simpa using slopeMoment_zero_le hR h hε
      · intro ι _ _ Ψ b B β ε h hε
        have h1 := slopeMoment_one_le hR h hε hc₁
        have hβ0 : 0 ≤ ballExpectation (extendedCutoff ρ p) Ψ β := ballExpectation_nonneg h.data h.weight_nonneg
        have hB := h.one_le
        have e : c₁ + 4 / ρ + B ≤ (c₁ + 4 / ρ + 1) * B ^ (0 + 1) := by
          have : 0 ≤ 4 / ρ := by positivity
          simp only [zero_add, pow_one]
          nlinarith
        exact h1.trans (mul_le_mul_of_nonneg_right e hβ0)
    | succ j ih =>
      obtain ⟨⟨c0, hc0, h0⟩, ⟨c1, hc1, h1⟩⟩ := ih
      refine ⟨⟨c1, hc1, h1⟩, ?_⟩
      have hδ : (0 : ℝ) < 1 / (2 * ((j : ℝ) + 1)) := by positivity
      obtain ⟨C, hC0, hC⟩ := cutoffCurvature_le hρ hp hδ
      refine ⟨2 * ((j : ℝ) + 1) * C * c0 + 2 * (4 / ρ + 1) * c1, by positivity, ?_⟩
      intro ι _ _ Ψ b B β ε h hε
      have hs := slopeMoment_add_two_le hR h hε hC0 hC
      have a0 := h0 ι Ψ b B β ε h hε
      have a1 := h1 ι Ψ b B β ε h hε
      have hB := h.one_le
      have hβ0 : 0 ≤ ballExpectation (extendedCutoff ρ p) Ψ β := ballExpectation_nonneg h.data h.weight_nonneg
      set m := ballExpectation (extendedCutoff ρ p) Ψ β with hm
      have hB0 : 0 < B := by linarith
      have hpj : 0 < B ^ j := by positivity
      have t1 : 2 * ((j : ℝ) + 1) * C * slopeMoment ρ p Ψ b ε j ≤
          2 * ((j : ℝ) + 1) * C * c0 * B ^ (j + 1 + 1) * m := by
        have s1 : c0 * B ^ j * m ≤ c0 * B ^ (j + 1 + 1) * m := by
          have : B ^ j ≤ B ^ (j + 1 + 1) := pow_le_pow_right₀ hB (by omega)
          exact mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left this hc0) hβ0
        have := mul_le_mul_of_nonneg_left (a0.trans s1)
          (by positivity : 0 ≤ 2 * ((j : ℝ) + 1) * C)
        linarith
      have t2 : 2 * (4 / ρ + B) * slopeMoment ρ p Ψ b ε (j + 1) ≤
          2 * (4 / ρ + 1) * c1 * B ^ (j + 1 + 1) * m := by
        have s0 : 4 / ρ + B ≤ (4 / ρ + 1) * B := by
          have : 0 ≤ 4 / ρ := by positivity
          nlinarith
        have s1 : 2 * (4 / ρ + B) * slopeMoment ρ p Ψ b ε (j + 1) ≤
            2 * (4 / ρ + B) * (c1 * B ^ (j + 1) * m) :=
          mul_le_mul_of_nonneg_left a1 (by positivity)
        have s2 : 2 * (4 / ρ + B) * (c1 * B ^ (j + 1) * m) ≤
            2 * ((4 / ρ + 1) * B) * (c1 * B ^ (j + 1) * m) := by
          apply mul_le_mul_of_nonneg_right _ (by positivity)
          linarith
        have e : 2 * ((4 / ρ + 1) * B) * (c1 * B ^ (j + 1) * m) =
            2 * (4 / ρ + 1) * c1 * B ^ (j + 1 + 1) * m := by
          rw [pow_succ B (j + 1)]
          ring
        linarith
      have : slopeMoment ρ p Ψ b ε (j + 1 + 1) ≤
          (2 * ((j : ℝ) + 1) * C * c0 + 2 * (4 / ρ + 1) * c1) * B ^ (j + 1 + 1) * m := by
        have e : (2 * ((j : ℝ) + 1) * C * c0 + 2 * (4 / ρ + 1) * c1) * B ^ (j + 1 + 1) * m =
            2 * ((j : ℝ) + 1) * C * c0 * B ^ (j + 1 + 1) * m +
              2 * (4 / ρ + 1) * c1 * B ^ (j + 1 + 1) * m := by
          ring
        rw [e]
        linarith
      exact this
  exact (two j).1
end YangMills.Construction.ColdStepAtMirrorFrames.ThirdDerivative
end
noncomputable section
open MeasureTheory Set
namespace YangMills.Construction.ColdStepAtMirrorFrames.ThirdDerivative
variable {ρ : ℝ} {p : ℝ → ℝ} {ε : ℝ}
theorem fderiv_norm_apply {v : BondVector} (hv : v ≠ 0) (e : BondVector) :
    fderiv ℝ (fun w : BondVector => ‖w‖) v e = inner ℝ v e / ‖v‖ := by
  have hd : DifferentiableAt ℝ (fun w : BondVector => ‖w‖) v :=
    (contDiffAt_norm (n := 1) ℝ hv).differentiableAt (by norm_num)
  have h1 := hd.hasFDerivAt.pow 2
  have h2 := (hasStrictFDerivAt_norm_sq v).hasFDerivAt
  have h3 := h1.unique h2
  have h4 := congrArg (fun L : BondVector →L[ℝ] ℝ => L e) h3
  simp at h4
  have hn : ‖v‖ ≠ 0 := norm_ne_zero_iff.mpr hv
  rw [eq_div_iff hn]
  have e2 : inner ℝ v e = ‖v‖ * fderiv ℝ (fun w : BondVector => ‖w‖) v e := by
    linarith
  rw [e2]
  ring
theorem norm_fderiv_norm_le_one (v : BondVector) : ‖fderiv ℝ (fun w : BondVector => ‖w‖) v‖ ≤ 1 := by
  have := norm_fderiv_le_of_lipschitz (𝕜 := ℝ) (f := fun w : BondVector => ‖w‖) (x₀ := v)
    (C := 1) (lipschitzWith_one_norm)
  simpa using this
theorem radialFn_contDiff_of_const {f : ℝ → ℝ} (hf : ContDiff ℝ 1 f) {c : ℝ} (hc : 0 < c)
    (h0 : ∀ u, u < c → f u = f 0) : ContDiff ℝ 1 (fun v : BondVector => f ‖v‖) := by
  rw [contDiff_iff_contDiffAt]
  intro v
  by_cases hv : v = 0
  · subst hv
    have : (fun v : BondVector => f ‖v‖) =ᶠ[nhds 0] fun _ => f 0 := by
      have hb : Metric.ball (0 : BondVector) c ∈ nhds (0 : BondVector) :=
        Metric.ball_mem_nhds _ hc
      filter_upwards [hb] with w hw
      exact h0 _ (by simpa using hw)
    exact contDiffAt_const.congr_of_eventuallyEq this
  · exact hf.contDiffAt.comp v (contDiffAt_norm ℝ hv)
theorem radialFn_fderiv_apply {f f' : ℝ → ℝ} (hd : ∀ u, HasDerivAt f (f' u) u) {c : ℝ} (hc : 0 < c)
    (h0 : ∀ u, u < c → f u = f 0) (v e : BondVector) :
    fderiv ℝ (fun v : BondVector => f ‖v‖) v e = f' ‖v‖ / ‖v‖ * inner ℝ v e := by
  by_cases hv : v = 0
  · subst hv
    have : (fun v : BondVector => f ‖v‖) =ᶠ[nhds 0] fun _ => f 0 := by
      have hb : Metric.ball (0 : BondVector) c ∈ nhds (0 : BondVector) :=
        Metric.ball_mem_nhds _ hc
      filter_upwards [hb] with w hw
      exact h0 _ (by simpa using hw)
    rw [this.fderiv_eq]
    simp
  · have hn : DifferentiableAt ℝ (fun w : BondVector => ‖w‖) v :=
      (contDiffAt_norm (n := 1) ℝ hv).differentiableAt (by norm_num)
    have h1 := (hd ‖v‖).comp_hasFDerivAt v hn.hasFDerivAt
    have h2 : fderiv ℝ (fun v : BondVector => f ‖v‖) v = _ := h1.fderiv
    rw [h2]
    simp only [_root_.smul_apply, smul_eq_mul, fderiv_norm_apply hv]
    ring
theorem norm_radialFn_fderiv_le {f f' : ℝ → ℝ} (hd : ∀ u, HasDerivAt f (f' u) u) {c : ℝ} (hc : 0 < c)
    (h0 : ∀ u, u < c → f u = f 0) (v : BondVector) :
    ‖fderiv ℝ (fun v : BondVector => f ‖v‖) v‖ ≤ |f' ‖v‖| := by
  by_cases hv : v = 0
  · subst hv
    have : (fun v : BondVector => f ‖v‖) =ᶠ[nhds 0] fun _ => f 0 := by
      have hb : Metric.ball (0 : BondVector) c ∈ nhds (0 : BondVector) :=
        Metric.ball_mem_nhds _ hc
      filter_upwards [hb] with w hw
      exact h0 _ (by simpa using hw)
    rw [this.fderiv_eq]
    simp
  · have hn : DifferentiableAt ℝ (fun w : BondVector => ‖w‖) v :=
      (contDiffAt_norm (n := 1) ℝ hv).differentiableAt (by norm_num)
    have h1 := (hd ‖v‖).comp_hasFDerivAt v hn.hasFDerivAt
    have h2 : fderiv ℝ (fun v : BondVector => f ‖v‖) v = _ := h1.fderiv
    rw [h2, norm_smul, Real.norm_eq_abs]
    have := norm_fderiv_norm_le_one v
    nlinarith [abs_nonneg (f' ‖v‖)]
def levelRatioDeriv (ρ : ℝ) (p : ℝ → ℝ) (ε u : ℝ) : ℝ :=
  - (deriv smoothStepMulDeriv (extendedCutoff ρ p u / ε) * (extendedCutoff ρ p u / ε)) * cutoffSlope ρ p u ^ 2 / u +
    smoothStepMulDeriv (extendedCutoff ρ p u / ε) * cutoffCurvature ρ p u / u -
    smoothStepMulDeriv (extendedCutoff ρ p u / ε) * cutoffSlope ρ p u / u ^ 2
theorem levelRatio_hasDerivAt (hR : CutoffFactorIsRadialCutoff) (hρ : 0 < ρ) (hp : IsCutoff ρ p) (hε : 0 < ε) (u : ℝ) :
    HasDerivAt (levelRatio ρ p ε) (levelRatioDeriv ρ p ε u) u := by
  rcases lt_or_ge u (5 * ρ / 8) with h0 | h0
  · have hev : levelRatio ρ p ε =ᶠ[nhds u] fun _ => 0 := by
      filter_upwards [Iio_mem_nhds h0] with v hv
      simp [levelRatio, cutoffSlope_inner hρ hp hv]
    have e : levelRatioDeriv ρ p ε u = 0 := by
      simp [levelRatioDeriv, cutoffSlope_inner hρ hp h0, cutoffCurvature_inner hρ hp h0]
    rw [e]
    exact (hasDerivAt_const u (0 : ℝ)).congr_of_eventuallyEq hev
  rcases lt_or_ge u ρ with h1 | h1
  · have hu : u ≠ 0 := by
      have : 0 < u := by linarith
      exact this.ne'
    have a1 := (extendedCutoff_hasDerivAt hρ hp h1).div_const ε
    have a2 : HasDerivAt smoothStepMulDeriv (deriv smoothStepMulDeriv (extendedCutoff ρ p u / ε)) (extendedCutoff ρ p u / ε) :=
      ((smoothStepMulDeriv_contDiff.differentiable (by simp)) _).hasDerivAt
    have a3 := a2.comp u a1
    have a4 := cutoffSlope_hasDerivAt hρ hp h1
    have a5 := (a3.mul a4).div (hasDerivAt_id u) hu
    refine HasDerivAt.congr_deriv a5 ?_
    simp only [levelRatioDeriv, id, Function.comp, Pi.mul_apply]
    field_simp
    try ring
  · have hev : levelRatio ρ p ε =ᶠ[nhds u] fun _ => 0 := by
      filter_upwards [eventually_extendedCutoff_div_lt_one hR hρ hp hε h1] with v hv
      simp [levelRatio, smoothStepMulDeriv_of_lt_one hv]
    have e : levelRatioDeriv ρ p ε u = 0 := by
      have e1 : extendedCutoff ρ p u / ε = 0 := by simp [extendedCutoff_eq_zero hR hρ hp h1]
      simp only [levelRatioDeriv, e1, smoothStepMulDeriv_of_lt_one (zero_lt_one' ℝ), smoothStepMulDeriv_deriv_of_lt_one (zero_lt_one' ℝ)]
      simp
    rw [e]
    exact (hasDerivAt_const u (0 : ℝ)).congr_of_eventuallyEq hev
theorem levelRatio_eq (ρ : ℝ) (p : ℝ → ℝ) (ε : ℝ) :
    levelRatio ρ p ε = fun u => (cutoffSlope ρ p u / u) * smoothStepMulDeriv (extendedCutoff ρ p u / ε) := by
  funext u
  simp only [levelRatio]
  ring
theorem levelRatio_contDiff (hR : CutoffFactorIsRadialCutoff) (hρ : 0 < ρ) (hp : IsCutoff ρ p) (hε : 0 < ε) :
    ContDiff ℝ 1 (levelRatio ρ p ε) := by
  rw [levelRatio_eq]
  exact contDiff_mul_comp_extendedCutoff hR hρ hp hε (smoothStepMulDeriv_contDiff.of_le (by simp)) (fun s hs => smoothStepMulDeriv_of_lt_one hs)
    fun u hu => cutoffSlope_div_contDiffAt hρ hp hu
theorem levelRatio_inner (hρ : 0 < ρ) (hp : IsCutoff ρ p) {u : ℝ} (h : u < 5 * ρ / 8) : levelRatio ρ p ε u = 0 := by
  simp [levelRatio, cutoffSlope_inner hρ hp h]
theorem levelStep_inner (hρ : 0 < ρ) (hp : IsCutoff ρ p) {u : ℝ} (h : u < 5 * ρ / 8) :
    levelStep ρ p ε u = levelStep ρ p ε 0 := by
  simp [levelStep, extendedCutoff_inner hρ hp h, extendedCutoff_inner hρ hp (by positivity : (0 : ℝ) < 5 * ρ / 8)]
theorem le_const_mul_of_nonneg {c₀ a C₁ : ℝ} (h0 : 1 ≤ c₀) (ha : 0 ≤ a) (hC : 0 ≤ C₁) :
    c₀ ≤ c₀ * (1 + a) * (1 + a) * (2 + C₁) ∧ c₀ * a ≤ c₀ * (1 + a) * (1 + a) * (2 + C₁) := by
  have h1 : (1 : ℝ) ≤ (1 + a) * (1 + a) * (2 + C₁) := by
    have e : (1 + a) * (1 + a) * (2 + C₁) = 2 + C₁ + 4 * a + 2 * (a * C₁) + 2 * (a * a) + (a * a) * C₁ := by
      ring
    have := mul_nonneg ha hC
    have := mul_nonneg ha ha
    have := mul_nonneg (mul_nonneg ha ha) hC
    linarith
  have h2 : a ≤ (1 + a) * (1 + a) * (2 + C₁) := by
    have e : (1 + a) * (1 + a) * (2 + C₁) = 2 + C₁ + 4 * a + 2 * (a * C₁) + 2 * (a * a) + (a * a) * C₁ := by
      ring
    have := mul_nonneg ha hC
    have := mul_nonneg ha ha
    have := mul_nonneg (mul_nonneg ha ha) hC
    linarith
  have e : c₀ * (1 + a) * (1 + a) * (2 + C₁) = c₀ * ((1 + a) * (1 + a) * (2 + C₁)) := by ring
  rw [e]
  have hc : 0 ≤ c₀ := by linarith
  exact ⟨by nlinarith, mul_le_mul_of_nonneg_left h2 hc⟩
theorem weighted_sum_le {c₀ a C₁ P0 P1 P2 : ℝ} (h0 : 1 ≤ c₀) (ha : 0 ≤ a) (hC : 0 ≤ C₁) (p0 : 0 ≤ P0)
    (p1 : 0 ≤ P1) (p2 : 0 ≤ P2) :
    c₀ * P2 + c₀ * (P2 + C₁ * P0) + c₀ * (a * P1) ≤
      c₀ * (1 + a) * (1 + a) * (2 + C₁) * (P0 + P1 + P2) := by
  have hc : 0 ≤ c₀ := by linarith
  have e1 : c₀ * P2 + c₀ * (P2 + C₁ * P0) + c₀ * (a * P1) = c₀ * (2 * P2 + C₁ * P0 + a * P1) := by
    ring
  have e2 : c₀ * (1 + a) * (1 + a) * (2 + C₁) * (P0 + P1 + P2) =
      c₀ * ((1 + a) * (1 + a) * (2 + C₁) * (P0 + P1 + P2)) := by ring
  rw [e1, e2]
  apply mul_le_mul_of_nonneg_left _ hc
  have t1 : 0 ≤ C₁ * (P1 + P2) := mul_nonneg hC (add_nonneg p1 p2)
  have t2 : 0 ≤ (3 * a + 2 * (a * C₁) + 2 * (a * a) + (a * a) * C₁) * (P0 + P1 + P2) := by
    apply mul_nonneg _ (by linarith)
    have := mul_nonneg ha hC
    have := mul_nonneg ha ha
    have := mul_nonneg (mul_nonneg ha ha) hC
    linarith
  have t3 : 0 ≤ a * (P0 + P2) := mul_nonneg ha (add_nonneg p0 p2)
  linarith
theorem rim_terms_le_of_numbers {c₀ a C₁ u π q K dKs T2 P0 P1 P2 L Ld : ℝ} (h0 : 1 ≤ c₀) (ha : 0 ≤ a)
    (hC : 0 ≤ C₁) (hπ : 0 ≤ π) (hq : 0 ≤ q) (hT : 0 ≤ T2) (p0 : 0 ≤ P0) (p1 : 0 ≤ P1) (p2 : 0 ≤ P2)
    (b1 : |K| ≤ c₀ * T2) (b3 : |dKs| ≤ c₀ * T2)
    (f1 : T2 * π = P1) (f2 : T2 * π ^ 2 = P2) (f3 : T2 * q ≤ P2 + C₁ * P0)
    (hu : 0 < u) (hua : 1 / u ≤ a) (hL : L = K * π / u)
    (hLd : u * Ld = - dKs * π ^ 2 + K * q - K * π / u) :
    u * |L| ≤ c₀ * P1 ∧ |L| ≤ c₀ * (a * P1) ∧
      u * |Ld| ≤ c₀ * (1 + a) * (1 + a) * (2 + C₁) * (P0 + P1 + P2) := by
  have hc : 0 ≤ c₀ := by linarith
  have g1 : |K| * π ≤ c₀ * P1 := by
    rw [← f1]
    have := mul_le_mul_of_nonneg_right b1 hπ
    have e : c₀ * T2 * π = c₀ * (T2 * π) := by ring
    linarith
  have g2 : |K * π / u| ≤ c₀ * (a * P1) := by
    rw [abs_div, abs_mul, abs_of_nonneg hπ, abs_of_pos hu, div_eq_mul_one_div]
    have := mul_le_mul g1 hua (by positivity) (by positivity)
    have e : c₀ * P1 * a = c₀ * (a * P1) := by ring
    linarith
  have g3 : u * |L| ≤ c₀ * P1 := by
    rw [hL, abs_div, abs_mul, abs_of_nonneg hπ, abs_of_pos hu]
    have : u * (|K| * π / u) = |K| * π := by
      field_simp
    rw [this]
    exact g1
  refine ⟨g3, by rw [hL]; exact g2, ?_⟩
  have t1 : |- dKs * π ^ 2| ≤ c₀ * P2 := by
    rw [abs_mul, abs_neg, abs_of_nonneg (sq_nonneg π), ← f2]
    have := mul_le_mul_of_nonneg_right b3 (sq_nonneg π)
    have e : c₀ * T2 * π ^ 2 = c₀ * (T2 * π ^ 2) := by ring
    linarith
  have t2 : |K * q| ≤ c₀ * (P2 + C₁ * P0) := by
    rw [abs_mul, abs_of_nonneg hq]
    have h2 := mul_le_mul_of_nonneg_right b1 hq
    have h3 := mul_le_mul_of_nonneg_left f3 hc
    have e : c₀ * T2 * q = c₀ * (T2 * q) := by ring
    linarith
  have e2 : u * |Ld| = |u * Ld| := by
    rw [abs_mul, abs_of_pos hu]
  rw [e2, hLd]
  have t4 := abs_sub (- dKs * π ^ 2 + K * q) (K * π / u)
  have t5 := abs_add_le (- dKs * π ^ 2) (K * q)
  have t6 := weighted_sum_le (P0 := P0) (P1 := P1) (P2 := P2) h0 ha hC p0 p1 p2
  linarith
theorem rim_terms_le (hρ : 0 < ρ) (hp : IsCutoff ρ p) : ∃ c : ℝ, 1 ≤ c ∧
    ∀ (ε u : ℝ), 0 < ε → 0 ≤ u → u < ρ → 0 ≤ extendedCutoff ρ p u →
      |levelStepDeriv ρ p ε u| ≤ c * (slopePower ρ p (ε / 2) 0 u + slopePower ρ p (ε / 2) 1 u + slopePower ρ p (ε / 2) 2 u) ∧
      u * |levelRatio ρ p ε u| ≤ c * (slopePower ρ p (ε / 2) 0 u + slopePower ρ p (ε / 2) 1 u + slopePower ρ p (ε / 2) 2 u) ∧
      |levelRatio ρ p ε u| ≤ c * (slopePower ρ p (ε / 2) 0 u + slopePower ρ p (ε / 2) 1 u + slopePower ρ p (ε / 2) 2 u) ∧
      u * |levelRatioDeriv ρ p ε u| ≤ c * (slopePower ρ p (ε / 2) 0 u + slopePower ρ p (ε / 2) 1 u + slopePower ρ p (ε / 2) 2 u) := by
  obtain ⟨c₀, hc₀, hb⟩ := smoothStep_bounds
  obtain ⟨C₁, hC₁0, hC₁⟩ := cutoffCurvature_le hρ hp (zero_lt_one' ℝ)
  have ha0 : 0 < 8 / (5 * ρ) := by positivity
  obtain ⟨k1, k2⟩ := le_const_mul_of_nonneg hc₀ ha0.le hC₁0
  refine ⟨c₀ * (1 + 8 / (5 * ρ)) * (1 + 8 / (5 * ρ)) * (2 + C₁), by linarith, fun ε u hε hu0 hu hr => ?_⟩
  have hs0 : 0 ≤ extendedCutoff ρ p u / ε := div_nonneg hr hε.le
  have e2 : extendedCutoff ρ p u / (ε / 2) = 2 * (extendedCutoff ρ p u / ε) := by
    field_simp
  have hT20 := smoothStep_nonneg (2 * (extendedCutoff ρ p u / ε))
  have hπ0 : 0 ≤ cutoffSlope ρ p u := cutoffSlope_nonneg hρ hp hu
  have hq0 : 0 ≤ cutoffCurvature ρ p u := cutoffCurvature_nonneg hρ hp hu
  have ett : levelStep ρ p (ε / 2) u = smoothStep (2 * (extendedCutoff ρ p u / ε)) := by
    simp only [levelStep, e2]
  obtain ⟨b1, b2, b3⟩ := hb (extendedCutoff ρ p u / ε)
  have hks := smoothStepScaledDeriv_nonneg hs0
  have hC : cutoffCurvature ρ p u ≤ cutoffSlope ρ p u ^ 2 + C₁ := by
    have := hC₁ u hu
    rwa [one_mul] at this
  have hP00 : 0 ≤ slopePower ρ p (ε / 2) 0 u := slopePower_nonneg hρ hp 0 hu
  have hP10 : 0 ≤ slopePower ρ p (ε / 2) 1 u := slopePower_nonneg hρ hp 1 hu
  have hP20 : 0 ≤ slopePower ρ p (ε / 2) 2 u := slopePower_nonneg hρ hp 2 hu
  have hinner : u < 5 * ρ / 8 ∨ outerStep ρ u = 1 := by
    rcases lt_or_ge u (5 * ρ / 8) with h | h
    · exact Or.inl h
    · exact Or.inr (outerStep_of_ge hρ (by linarith))
  have f1 : smoothStep (2 * (extendedCutoff ρ p u / ε)) * cutoffSlope ρ p u = slopePower ρ p (ε / 2) 1 u := by
    simp only [slopePower, ett, pow_one]
    rcases hinner with h | h
    · simp [cutoffSlope_inner hρ hp h]
    · rw [h]
      ring
  have f2 : smoothStep (2 * (extendedCutoff ρ p u / ε)) * cutoffSlope ρ p u ^ 2 = slopePower ρ p (ε / 2) 2 u := by
    simp only [slopePower, ett]
    rcases hinner with h | h
    · simp [cutoffSlope_inner hρ hp h]
    · rw [h]
      ring
  have f3 : smoothStep (2 * (extendedCutoff ρ p u / ε)) * cutoffCurvature ρ p u ≤
      slopePower ρ p (ε / 2) 2 u + C₁ * slopePower ρ p (ε / 2) 0 u := by
    rcases hinner with h | h
    · rw [cutoffCurvature_inner hρ hp h, mul_zero]
      exact add_nonneg hP20 (mul_nonneg hC₁0 hP00)
    · have e0 : slopePower ρ p (ε / 2) 0 u = smoothStep (2 * (extendedCutoff ρ p u / ε)) := by
        simp only [slopePower, ett, h, pow_zero, mul_one, one_mul]
      rw [e0, ← f2]
      have := mul_le_mul_of_nonneg_left hC hT20
      linarith
  set Sg := slopePower ρ p (ε / 2) 0 u + slopePower ρ p (ε / 2) 1 u + slopePower ρ p (ε / 2) 2 u with hSg
  have hSg0 : 0 ≤ Sg := add_nonneg (add_nonneg hP00 hP10) hP20
  set c := c₀ * (1 + 8 / (5 * ρ)) * (1 + 8 / (5 * ρ)) * (2 + C₁) with hc
  have hP1S : slopePower ρ p (ε / 2) 1 u ≤ Sg := by
    simp only [hSg]
    linarith
  have hc0 : 0 ≤ c₀ := by linarith
  have hcP : c₀ * slopePower ρ p (ε / 2) 1 u ≤ c * Sg :=
    mul_le_mul k1 hP1S hP10 (by linarith)
  have hcaP : c₀ * ((8 / (5 * ρ)) * slopePower ρ p (ε / 2) 1 u) ≤ c * Sg := by
    have e : c₀ * ((8 / (5 * ρ)) * slopePower ρ p (ε / 2) 1 u) = (c₀ * (8 / (5 * ρ))) * slopePower ρ p (ε / 2) 1 u := by
      ring
    rw [e]
    exact mul_le_mul k2 hP1S hP10 (by linarith)
  have httd : |levelStepDeriv ρ p ε u| ≤ c * Sg := by
    have e : levelStepDeriv ρ p ε u = - (smoothStepScaledDeriv (extendedCutoff ρ p u / ε) * cutoffSlope ρ p u) := by
      simp only [levelStepDeriv]
      ring
    rw [e, abs_neg, abs_of_nonneg (mul_nonneg hks hπ0)]
    have h1 := mul_le_mul_of_nonneg_right b2 hπ0
    have e3 : c₀ * smoothStep (2 * (extendedCutoff ρ p u / ε)) * cutoffSlope ρ p u = c₀ * slopePower ρ p (ε / 2) 1 u := by
      rw [← f1]
      ring
    linarith
  rcases lt_or_ge u (5 * ρ / 8) with h | h
  · have e1 : levelRatio ρ p ε u = 0 := levelRatio_inner hρ hp h
    have e2 : levelRatioDeriv ρ p ε u = 0 := by
      simp [levelRatioDeriv, cutoffSlope_inner hρ hp h, cutoffCurvature_inner hρ hp h]
    have hz : 0 ≤ c * Sg := mul_nonneg (by linarith) hSg0
    rw [e1, e2]
    refine ⟨httd, ?_, ?_, ?_⟩ <;> simpa using hz
  · have hu1 : 0 < u := by linarith
    have hua : 1 / u ≤ 8 / (5 * ρ) := by
      rw [div_le_div_iff₀ hu1 (by positivity)]
      linarith
    have hLd : u * levelRatioDeriv ρ p ε u = - (deriv smoothStepMulDeriv (extendedCutoff ρ p u / ε) * (extendedCutoff ρ p u / ε)) *
        cutoffSlope ρ p u ^ 2 + smoothStepMulDeriv (extendedCutoff ρ p u / ε) * cutoffCurvature ρ p u -
        smoothStepMulDeriv (extendedCutoff ρ p u / ε) * cutoffSlope ρ p u / u := by
      simp only [levelRatioDeriv]
      field_simp
    obtain ⟨r1, r2, r3⟩ := rim_terms_le_of_numbers hc₀ ha0.le hC₁0 hπ0 hq0 hT20 hP00 hP10 hP20 b1 b3 f1 f2 f3 hu1
      hua (L := levelRatio ρ p ε u) rfl hLd
    exact ⟨httd, r1.trans hcP, r2.trans hcaP, r3⟩
end YangMills.Construction.ColdStepAtMirrorFrames.ThirdDerivative
end
noncomputable section
open MeasureTheory Set
namespace YangMills.Construction.ColdStepAtMirrorFrames.ThirdDerivative
variable {ι : Type} [Fintype ι] [DecidableEq ι]
theorem bondGradNorm_nonneg (f : BondField ι → ℝ) (b : ι) (η : BondField ι) :
    0 ≤ bondGradNorm f b η := norm_nonneg _
theorem bondGradNorm_le {f : BondField ι → ℝ} {b : ι} {η : BondField ι} {M : ℝ} (hM : 0 ≤ M)
    (h : ∀ e : BondVector, |fderiv ℝ f η (bondVariation b e)| ≤ M * ‖e‖) : bondGradNorm f b η ≤ M := by apply _root_.YangMills.Construction.ColdStepAtMirrorFrames.LocalCalculus.bondGradNorm_le_of_forall <;> assumption
theorem abs_fderiv_bondVariation_le (f : BondField ι → ℝ) (b : ι) (η : BondField ι) (e : BondVector) :
    |fderiv ℝ f η (bondVariation b e)| ≤ bondGradNorm f b η * ‖e‖ := by apply _root_.YangMills.Construction.ColdStepAtMirrorFrames.LocalCalculus.abs_fderiv_bondVariation_le <;> assumption
theorem bondGradNorm_continuous {f : BondField ι → ℝ} (hf : ContDiff ℝ 1 f) (b : ι) :
    Continuous (fun η => bondGradNorm f b η) := by
  unfold bondGradNorm
  have h : Continuous (fderiv ℝ f) := hf.continuous_fderiv (by norm_num)
  exact ((ContinuousLinearMap.compL ℝ _ _ _).flip
    (ContinuousLinearMap.single ℝ (fun _ : ι => BondVector) b)).continuous.comp h |>.norm
theorem bondGradNorm_add_le {f g : BondField ι → ℝ} (hf : ContDiff ℝ 1 f) (hg : ContDiff ℝ 1 g)
    (b : ι) (η : BondField ι) :
    bondGradNorm (fun ζ => f ζ + g ζ) b η ≤ bondGradNorm f b η + bondGradNorm g b η := by
  apply bondGradNorm_le (add_nonneg (bondGradNorm_nonneg _ _ _) (bondGradNorm_nonneg _ _ _))
  intro e
  have h1 := ((hf.differentiable (by norm_num)) η).hasFDerivAt
  have h2 := ((hg.differentiable (by norm_num)) η).hasFDerivAt
  have h3 : fderiv ℝ (fun ζ => f ζ + g ζ) η = _ := (h1.add h2).fderiv
  rw [h3]
  simp only [_root_.add_apply]
  have a1 := abs_fderiv_bondVariation_le f b η e
  have a2 := abs_fderiv_bondVariation_le g b η e
  have := abs_add_le (fderiv ℝ f η (bondVariation b e)) (fderiv ℝ g η (bondVariation b e))
  nlinarith
theorem bondGradNorm_mul_le {f g : BondField ι → ℝ} (hf : ContDiff ℝ 1 f) (hg : ContDiff ℝ 1 g)
    (b : ι) (η : BondField ι) :
    bondGradNorm (fun ζ => f ζ * g ζ) b η ≤
      |f η| * bondGradNorm g b η + |g η| * bondGradNorm f b η := by
  apply bondGradNorm_le (add_nonneg (mul_nonneg (abs_nonneg _) (bondGradNorm_nonneg _ _ _))
    (mul_nonneg (abs_nonneg _) (bondGradNorm_nonneg _ _ _)))
  intro e
  have h1 := ((hf.differentiable (by norm_num)) η).hasFDerivAt
  have h2 := ((hg.differentiable (by norm_num)) η).hasFDerivAt
  have h3 : fderiv ℝ (fun ζ => f ζ * g ζ) η = _ := (h1.mul h2).fderiv
  rw [h3]
  simp only [_root_.add_apply, _root_.smul_apply, smul_eq_mul]
  have a1 := abs_fderiv_bondVariation_le f b η e
  have a2 := abs_fderiv_bondVariation_le g b η e
  have b1 := abs_add_le (f η * fderiv ℝ g η (bondVariation b e)) (g η * fderiv ℝ f η (bondVariation b e))
  rw [abs_mul, abs_mul] at b1
  have c1 := mul_le_mul_of_nonneg_left a2 (abs_nonneg (f η))
  have c2 := mul_le_mul_of_nonneg_left a1 (abs_nonneg (g η))
  nlinarith
theorem bondGradNorm_sub_const {f : BondField ι → ℝ} (c : ℝ) (b : ι) (η : BondField ι) :
    bondGradNorm (fun ζ => f ζ - c) b η = bondGradNorm f b η := by
  unfold bondGradNorm
  rw [fderiv_sub_const]
theorem contDiff_comp_apply {φ : BondVector → ℝ} {n : WithTop ℕ∞} (hφ : ContDiff ℝ n φ) (b : ι) :
    ContDiff ℝ n (fun η : BondField ι => φ (η b)) :=
  hφ.comp (contDiff_apply ℝ BondVector b)
theorem hasFDerivAt_comp_apply {φ : BondVector → ℝ} (hφ : ContDiff ℝ 1 φ) (b : ι) (η : BondField ι) :
    HasFDerivAt (fun ζ : BondField ι => φ (ζ b))
      ((fderiv ℝ φ (η b)).comp (ContinuousLinearMap.proj b)) η := by
  have h1 := ((hφ.differentiable (by norm_num)) (η b)).hasFDerivAt
  exact h1.comp η (ContinuousLinearMap.proj (R := ℝ) (φ := fun _ : ι => BondVector) b).hasFDerivAt
theorem bondGradNorm_comp_apply_le {φ : BondVector → ℝ} (hφ : ContDiff ℝ 1 φ) (b b' : ι) (η : BondField ι) :
    bondGradNorm (fun ζ : BondField ι => φ (ζ b)) b' η ≤
      if b' = b then ‖fderiv ℝ φ (η b)‖ else 0 := by
  apply bondGradNorm_le (by split_ifs <;> simp)
  intro e
  rw [(hasFDerivAt_comp_apply hφ b η).fderiv]
  simp only [ContinuousLinearMap.comp_apply, ContinuousLinearMap.proj_apply, bondVariation]
  by_cases h : b' = b
  · subst h
    simp only [Pi.single_eq_same, if_true]
    simpa using (fderiv ℝ φ (η b')).le_opNorm e
  · simp [h, Pi.single_eq_of_ne (Ne.symm h)]
end YangMills.Construction.ColdStepAtMirrorFrames.ThirdDerivative
end
noncomputable section
open MeasureTheory Set Filter Topology
namespace YangMills.Construction.ColdStepAtMirrorFrames.ThirdDerivative
variable {ι : Type} [Fintype ι] [DecidableEq ι]
variable {ρ : ℝ} {p : ℝ → ℝ} {Ψ : BondField ι → ℝ} {ε : ℝ} {α : BondVector → ℝ} {e : BondVector}
def cutCoefficient (ρ : ℝ) (p : ℝ → ℝ) (ε : ℝ) (α : BondVector → ℝ) (v : BondVector) : ℝ :=
  α v * levelStep ρ p ε ‖v‖
def localTerm (ρ : ℝ) (p : ℝ → ℝ) (ε : ℝ) (α : BondVector → ℝ) (e v : BondVector) : ℝ :=
  - (levelStep ρ p ε ‖v‖ * fderiv ℝ α v e) + α v * (levelRatio ρ p ε ‖v‖ * inner ℝ v e)
def byPartsTerm (ρ : ℝ) (p : ℝ → ℝ) (ε : ℝ) (α : BondVector → ℝ) (Ψ : BondField ι → ℝ) (b : ι)
    (e : BondVector) (η : BondField ι) : ℝ :=
  cutCoefficient ρ p ε α (η b) * bondPartialDeriv Ψ b η e + localTerm ρ p ε α e (η b)
theorem levelStep_norm_contDiff (hR : CutoffFactorIsRadialCutoff) (hρ : 0 < ρ) (hp : IsCutoff ρ p) :
    ContDiff ℝ 1 (fun v : BondVector => levelStep ρ p ε ‖v‖) :=
  radialFn_contDiff_of_const (levelStep_contDiff hR hρ hp) (by positivity : 0 < 5 * ρ / 8)
    fun u hu => levelStep_inner hρ hp hu
theorem levelRatio_norm_contDiff (hR : CutoffFactorIsRadialCutoff) (hρ : 0 < ρ) (hp : IsCutoff ρ p) (hε : 0 < ε) :
    ContDiff ℝ 1 (fun v : BondVector => levelRatio ρ p ε ‖v‖) :=
  radialFn_contDiff_of_const (levelRatio_contDiff hR hρ hp hε) (by positivity : 0 < 5 * ρ / 8)
    fun u hu => by
      rw [levelRatio_inner hρ hp hu, levelRatio_inner hρ hp (by positivity : (0 : ℝ) < 5 * ρ / 8)]
theorem inner_left_contDiff (e : BondVector) : ContDiff ℝ 1 (fun v : BondVector => inner ℝ v e) :=
  contDiff_id.inner ℝ contDiff_const
theorem fderiv_apply_contDiff (hα : ContDiff ℝ 2 α) (e : BondVector) :
    ContDiff ℝ 1 (fun v => fderiv ℝ α v e) :=
  (hα.fderiv_right (m := 1) (by norm_num)).clm_apply contDiff_const
theorem cutCoefficient_contDiff (hR : CutoffFactorIsRadialCutoff) (hρ : 0 < ρ) (hp : IsCutoff ρ p)
    (hα : ContDiff ℝ 2 α) : ContDiff ℝ 1 (cutCoefficient ρ p ε α) :=
  (hα.of_le (by norm_num)).mul (levelStep_norm_contDiff hR hρ hp)
theorem localTerm_contDiff (hR : CutoffFactorIsRadialCutoff) (hρ : 0 < ρ) (hp : IsCutoff ρ p) (hε : 0 < ε)
    (hα : ContDiff ℝ 2 α) (e : BondVector) : ContDiff ℝ 1 (localTerm ρ p ε α e) :=
  ((levelStep_norm_contDiff hR hρ hp).mul (fderiv_apply_contDiff hα e)).neg.add
    ((hα.of_le (by norm_num)).mul ((levelRatio_norm_contDiff hR hρ hp hε).mul (inner_left_contDiff e)))
theorem bondPartialDeriv_contDiff {f : BondField ι → ℝ} {n : WithTop ℕ∞} (hf : ContDiff ℝ (n + 1) f)
    (b : ι) (e : BondVector) : ContDiff ℝ n (fun η => bondPartialDeriv f b η e) :=
  (hf.fderiv_right (m := n) le_rfl).clm_apply contDiff_const
theorem bondPartialDeriv_continuous {f : BondField ι → ℝ} (hf : ContDiff ℝ 1 f) (b : ι) (e : BondVector) :
    Continuous (fun η => bondPartialDeriv f b η e) :=
  (hf.continuous_fderiv (by norm_num)).clm_apply continuous_const
theorem byPartsTerm_contDiff (hR : CutoffFactorIsRadialCutoff) (hρ : 0 < ρ) (hp : IsCutoff ρ p) (hε : 0 < ε)
    (hα : ContDiff ℝ 2 α) (hΨ : ContDiff ℝ 3 Ψ) (b : ι) (e : BondVector) :
    ContDiff ℝ 1 (byPartsTerm ρ p ε α Ψ b e) := by
  have h2 : ContDiff ℝ 1 (fun η => bondPartialDeriv Ψ b η e) :=
    bondPartialDeriv_contDiff (n := 1) (hΨ.of_le (by norm_num)) b e
  exact ((contDiff_comp_apply (cutCoefficient_contDiff hR hρ hp hα) b).mul h2).add
    (contDiff_comp_apply (localTerm_contDiff hR hρ hp hε hα e) b)
theorem radialWeightProd_fderiv_bondVariation {r : ℝ → ℝ} (hd : IsCutoffMeasureData ρ r Ψ) (η : BondField ι) (b : ι)
    (e : BondVector) :
    fderiv ℝ (radialWeightProd (ι := ι) r) η (bondVariation b e) =
      (∏ b' ∈ Finset.univ.erase b, r ‖η b'‖) * fderiv ℝ (fun v : BondVector => r ‖v‖) (η b) e := by
  have hdiff : Differentiable ℝ (radialWeightProd (ι := ι) r) :=
    (radialWeightProd_contDiff hd).differentiable (by norm_num)
  have hline := hasDerivAt_line_fderiv hdiff η (bondVariation b e)
  set c : ℝ := ∏ b' ∈ Finset.univ.erase b, r ‖η b'‖ with hc
  have hψ : Differentiable ℝ (fun v : BondVector => r ‖v‖) :=
    (radialWeight_contDiff hd).differentiable (by norm_num)
  have h1 : HasDerivAt (fun s : ℝ => η b + s • e) e 0 := by
    have := ((hasDerivAt_id (0 : ℝ)).smul_const e).const_add (η b)
    simpa using this
  have h2 : HasFDerivAt (fun v : BondVector => r ‖v‖) (fderiv ℝ (fun v : BondVector => r ‖v‖) (η b))
      (η b + (0 : ℝ) • e) := by
    simpa using (hψ (η b)).hasFDerivAt
  have h3 := (h2.comp_hasDerivAt (0 : ℝ) h1).const_mul c
  have heq : (fun s : ℝ => radialWeightProd r (η + s • bondVariation b e)) =
      fun s : ℝ => c * (((fun v : BondVector => r ‖v‖) ∘ fun s : ℝ => η b + s • e) s) := by
    funext s
    unfold radialWeightProd
    rw [← Finset.mul_prod_erase Finset.univ _ (Finset.mem_univ b), mul_comm]
    congr 1
    · apply Finset.prod_congr rfl
      intro b' hb'
      have hne : b' ≠ b := Finset.ne_of_mem_erase hb'
      simp [bondVariation, Pi.single_eq_of_ne hne]
    · simp [bondVariation]
  rw [← heq] at h3
  exact hline.unique h3
theorem levelStep_mul_ballDensity_fderiv (hR : CutoffFactorIsRadialCutoff) (hρ : 0 < ρ) (hp : IsCutoff ρ p) (hε : 0 < ε)
    (hd : IsCutoffMeasureData ρ (extendedCutoff ρ p) Ψ) (η : BondField ι) (b : ι) (e : BondVector) :
    levelStep ρ p ε ‖η b‖ * fderiv ℝ (ballDensity (extendedCutoff ρ p) Ψ) η (bondVariation b e) =
      levelStep ρ p ε ‖η b‖ * (- (cutoffSlope ρ p ‖η b‖ / ‖η b‖ * inner ℝ (η b) e) - bondPartialDeriv Ψ b η e) *
        ballDensity (extendedCutoff ρ p) Ψ η := by
  rcases lt_or_ge ‖η b‖ ρ with hu | hu
  · rw [ballDensity_fderiv hd, radialWeightProd_fderiv_bondVariation hd]
    have hdr : ∀ u, HasDerivAt (extendedCutoff ρ p) (deriv (extendedCutoff ρ p) u) u := fun u =>
      (((extendedCutoff_contDiff hR hρ hp).differentiable (by norm_num)) u).hasDerivAt
    have h1 := radialFn_fderiv_apply hdr (by positivity : 0 < 5 * ρ / 8) (fun u hu' => by
      rw [extendedCutoff_inner hρ hp hu', extendedCutoff_inner hρ hp (by positivity : (0 : ℝ) < 5 * ρ / 8)])
      (η b) e
    rw [h1, (extendedCutoff_hasDerivAt hρ hp hu).deriv]
    have e2 : radialWeightProd (extendedCutoff ρ p) η = (∏ b' ∈ Finset.univ.erase b, extendedCutoff ρ p ‖η b'‖) *
        extendedCutoff ρ p ‖η b‖ := by
      unfold radialWeightProd
      rw [← Finset.mul_prod_erase Finset.univ _ (Finset.mem_univ b), mul_comm]
    simp only [ballDensity, bondPartialDeriv, e2, bondVariation]
    ring
  · simp [levelStep_eq_zero hR hρ hp hε hu]
theorem cutCoefficient_fderiv_apply (hR : CutoffFactorIsRadialCutoff) (hρ : 0 < ρ) (hp : IsCutoff ρ p) (hε : 0 < ε)
    (hα : ContDiff ℝ 2 α) (v e : BondVector) :
    fderiv ℝ (cutCoefficient ρ p ε α) v e =
      α v * (levelStepDeriv ρ p ε ‖v‖ / ‖v‖ * inner ℝ v e) + levelStep ρ p ε ‖v‖ * fderiv ℝ α v e := by
  have h1 := (((hα.of_le (by norm_num : (1 : WithTop ℕ∞) ≤ 2)).differentiable (by norm_num)) v).hasFDerivAt
  have h2 := (((levelStep_norm_contDiff (ε := ε) hR hρ hp).differentiable (by norm_num)) v).hasFDerivAt
  have h3 : fderiv ℝ (cutCoefficient ρ p ε α) v = _ := (h1.mul h2).fderiv
  rw [h3]
  simp only [_root_.add_apply, _root_.smul_apply, smul_eq_mul]
  rw [radialFn_fderiv_apply (levelStep_hasDerivAt hR hρ hp hε) (by positivity : 0 < 5 * ρ / 8)
    (fun u hu => levelStep_inner hρ hp hu) v e]
theorem levelRatio_identity (ε u : ℝ) (hu : 0 ≤ u) :
    (levelStep ρ p ε u * cutoffSlope ρ p u - levelStepDeriv ρ p ε u) / u = levelRatio ρ p ε u := by
  simp only [levelStep, levelStepDeriv, levelRatio, smoothStepMulDeriv]
  ring
theorem ballExpectation_by_parts (hR : CutoffFactorIsRadialCutoff) (hρ : 0 < ρ) (hp : IsCutoff ρ p) (hε : 0 < ε)
    (hd : IsCutoffMeasureData ρ (extendedCutoff ρ p) Ψ) (hα : ContDiff ℝ 2 α) (b : ι) (e : BondVector)
    {A : BondField ι → ℝ} (hA : ContDiff ℝ 1 A) :
    ballExpectation (extendedCutoff ρ p) Ψ (fun η => bondPartialDeriv A b η e * cutCoefficient ρ p ε α (η b)) =
      ballExpectation (extendedCutoff ρ p) Ψ (fun η => A η * byPartsTerm ρ p ε α Ψ b e η) := by
  have hc := cutCoefficient_contDiff (ε := ε) hR hρ hp hα
  have hcb : ContDiff ℝ 1 (fun η : BondField ι => cutCoefficient ρ p ε α (η b)) := contDiff_comp_apply hc b
  have hT : ContDiff ℝ 1 (fun η => A η * cutCoefficient ρ p ε α (η b)) := hA.mul hcb
  have hbp := integral_mul_fderiv_dir hT (ballDensity_contDiff hd) (ballDensity_hasCompactSupport hd) (bondVariation b e)
  have hF : ∀ η, fderiv ℝ (fun ζ => A ζ * cutCoefficient ρ p ε α (ζ b)) η (bondVariation b e) =
      A η * fderiv ℝ (cutCoefficient ρ p ε α) (η b) e + cutCoefficient ρ p ε α (η b) * bondPartialDeriv A b η e := by
    intro η
    have h1 := ((hA.differentiable (by norm_num)) η).hasFDerivAt
    have h2 := hasFDerivAt_comp_apply hc b η
    have h3 : fderiv ℝ (fun ζ => A ζ * cutCoefficient ρ p ε α (ζ b)) η = _ := (h1.mul h2).fderiv
    rw [h3]
    simp [bondPartialDeriv, bondVariation]
  have hL : ∀ η, A η * cutCoefficient ρ p ε α (η b) *
        fderiv ℝ (ballDensity (extendedCutoff ρ p) Ψ) η (bondVariation b e) =
      A η * α (η b) * (levelStep ρ p ε ‖η b‖ * (- (cutoffSlope ρ p ‖η b‖ / ‖η b‖ * inner ℝ (η b) e) -
        bondPartialDeriv Ψ b η e)) * ballDensity (extendedCutoff ρ p) Ψ η := by
    intro η
    have := levelStep_mul_ballDensity_fderiv hR hρ hp hε hd η b e
    simp only [cutCoefficient]
    calc A η * (α (η b) * levelStep ρ p ε ‖η b‖) *
          fderiv ℝ (ballDensity (extendedCutoff ρ p) Ψ) η (bondVariation b e)
        = A η * α (η b) * (levelStep ρ p ε ‖η b‖ *
          fderiv ℝ (ballDensity (extendedCutoff ρ p) Ψ) η (bondVariation b e)) := by ring
      _ = _ := by rw [this]; ring
  simp only [hL, hF] at hbp
  simp only [ballExpectation_def]
  congr 1
  have hS : ∀ η, A η * byPartsTerm ρ p ε α Ψ b e η =
      A η * fderiv ℝ (cutCoefficient ρ p ε α) (η b) e * (-1) +
        (- (A η * α (η b) * (levelStep ρ p ε ‖η b‖ * (- (cutoffSlope ρ p ‖η b‖ / ‖η b‖ * inner ℝ (η b) e) -
          bondPartialDeriv Ψ b η e)))) := by
    intro η
    rw [cutCoefficient_fderiv_apply hR hρ hp hε hα]
    simp only [byPartsTerm, localTerm, cutCoefficient, ← levelRatio_identity ε _ (norm_nonneg _)]
    ring
  have cdc : Continuous fun η : BondField ι => fderiv ℝ (cutCoefficient ρ p ε α) (η b) e :=
    ((hc.continuous_fderiv (by norm_num)).comp (continuous_apply b)).clm_apply continuous_const
  have cAp : Continuous fun η => bondPartialDeriv A b η e := bondPartialDeriv_continuous hA b e
  have ccb : Continuous fun η : BondField ι => cutCoefficient ρ p ε α (η b) := hcb.continuous
  have i1 : Integrable (fun η => A η * fderiv ℝ (cutCoefficient ρ p ε α) (η b) e *
      ballDensity (extendedCutoff ρ p) Ψ η) := integrable_mul_ballDensity hd (hA.continuous.mul cdc)
  have i2 : Integrable (fun η => cutCoefficient ρ p ε α (η b) * bondPartialDeriv A b η e *
      ballDensity (extendedCutoff ρ p) Ψ η) := integrable_mul_ballDensity hd (ccb.mul cAp)
  have i3 : Integrable (fun η => A η * α (η b) * (levelStep ρ p ε ‖η b‖ *
      (- (cutoffSlope ρ p ‖η b‖ / ‖η b‖ * inner ℝ (η b) e) - bondPartialDeriv Ψ b η e)) *
        ballDensity (extendedCutoff ρ p) Ψ η) := by
    have h0 : Continuous fun η => fderiv ℝ (ballDensity (extendedCutoff ρ p) Ψ) η (bondVariation b e) :=
      ((ballDensity_contDiff hd).continuous_fderiv (by norm_num)).clm_apply continuous_const
    have : Integrable fun η => (A η * cutCoefficient ρ p ε α (η b)) *
        fderiv ℝ (ballDensity (extendedCutoff ρ p) Ψ) η (bondVariation b e) :=
      Continuous.integrable_of_hasCompactSupport (hT.continuous.mul h0)
        ((ballDensity_hasCompactSupport hd).fderiv_apply (𝕜 := ℝ) (bondVariation b e)).mul_left
    simpa only [hL] using this
  have e1 : ∫ η, (A η * fderiv ℝ (cutCoefficient ρ p ε α) (η b) e + cutCoefficient ρ p ε α (η b) * bondPartialDeriv A b η e) *
        ballDensity (extendedCutoff ρ p) Ψ η =
      (∫ η, A η * fderiv ℝ (cutCoefficient ρ p ε α) (η b) e * ballDensity (extendedCutoff ρ p) Ψ η) +
        ∫ η, cutCoefficient ρ p ε α (η b) * bondPartialDeriv A b η e * ballDensity (extendedCutoff ρ p) Ψ η := by
    simp only [add_mul]
    exact integral_add i1 i2
  have e2 : ∫ η, A η * byPartsTerm ρ p ε α Ψ b e η * ballDensity (extendedCutoff ρ p) Ψ η =
      - (∫ η, A η * fderiv ℝ (cutCoefficient ρ p ε α) (η b) e * ballDensity (extendedCutoff ρ p) Ψ η) -
        ∫ η, A η * α (η b) * (levelStep ρ p ε ‖η b‖ *
          (- (cutoffSlope ρ p ‖η b‖ / ‖η b‖ * inner ℝ (η b) e) - bondPartialDeriv Ψ b η e)) *
            ballDensity (extendedCutoff ρ p) Ψ η := by
    have hi : Integrable (fun η => -(A η * fderiv ℝ (cutCoefficient ρ p ε α) (η b) e *
        ballDensity (extendedCutoff ρ p) Ψ η)) := i1.neg
    have e0 := integral_sub hi i3
    rw [integral_neg] at e0
    rw [← e0]
    congr 1
    funext η
    rw [hS]
    ring
  have e3 : ∫ η, bondPartialDeriv A b η e * cutCoefficient ρ p ε α (η b) * ballDensity (extendedCutoff ρ p) Ψ η =
      ∫ η, cutCoefficient ρ p ε α (η b) * bondPartialDeriv A b η e * ballDensity (extendedCutoff ρ p) Ψ η := by
    congr 1
    funext η
    ring
  rw [e3, e2]
  rw [e1] at hbp
  linarith
theorem ballCovariance_by_parts (hR : CutoffFactorIsRadialCutoff) (hρ : 0 < ρ) (hp : IsCutoff ρ p) (hε : 0 < ε)
    (hd : IsCutoffMeasureData ρ (extendedCutoff ρ p) Ψ) (hα : ContDiff ℝ 2 α) (b : ι) (e : BondVector)
    {g H : BondField ι → ℝ} (hg : ContDiff ℝ 1 g) (hH : ContDiff ℝ 1 H) :
    ballCovariance (extendedCutoff ρ p) Ψ g (fun η => cutCoefficient ρ p ε α (η b) * bondPartialDeriv H b η e) =
      ballCovariance (extendedCutoff ρ p) Ψ g
          (fun η => (H η - ballExpectation (extendedCutoff ρ p) Ψ H) * byPartsTerm ρ p ε α Ψ b e η) -
        ballCovariance (extendedCutoff ρ p) Ψ H (fun η => cutCoefficient ρ p ε α (η b) * bondPartialDeriv g b η e) := by
  set mg := ballExpectation (extendedCutoff ρ p) Ψ g with hmg
  set mH := ballExpectation (extendedCutoff ρ p) Ψ H with hmH
  have hc : ContDiff ℝ 1 (fun η : BondField ι => cutCoefficient ρ p ε α (η b)) :=
    contDiff_comp_apply (cutCoefficient_contDiff hR hρ hp hα) b
  have cc := hc.continuous
  have cg := hg.continuous
  have cH := hH.continuous
  have cpg := bondPartialDeriv_continuous hg b e
  have cpH := bondPartialDeriv_continuous hH b e
  have cS : Continuous (byPartsTerm ρ p ε α Ψ b e) := (byPartsTerm_contDiff hR hρ hp hε hα hd.smooth b e).continuous
  have hA : ContDiff ℝ 1 (fun η => (g η - mg) * (H η - mH)) :=
    (hg.sub contDiff_const).mul (hH.sub contDiff_const)
  have hs := ballExpectation_by_parts hR hρ hp hε hd hα b e hA
  have hpart : ∀ η, bondPartialDeriv (fun ζ => (g ζ - mg) * (H ζ - mH)) b η e =
      (g η - mg) * bondPartialDeriv H b η e + (H η - mH) * bondPartialDeriv g b η e := by
    intro η
    have h1 := (((hg.sub (contDiff_const (c := mg))).differentiable (by norm_num)) η).hasFDerivAt
    have h2 := (((hH.sub (contDiff_const (c := mH))).differentiable (by norm_num)) η).hasFDerivAt
    have h3 : fderiv ℝ (fun ζ => (g ζ - mg) * (H ζ - mH)) η = _ := (h1.mul h2).fderiv
    simp only [bondPartialDeriv]
    rw [h3]
    simp only [_root_.add_apply, _root_.smul_apply, smul_eq_mul]
    rw [fderiv_sub_const, fderiv_sub_const]
  have ch1 : Continuous fun η => cutCoefficient ρ p ε α (η b) * bondPartialDeriv H b η e := cc.mul cpH
  have ch2 : Continuous fun η => (H η - mH) * byPartsTerm ρ p ε α Ψ b e η :=
    (cH.sub continuous_const).mul cS
  have ch3 : Continuous fun η => cutCoefficient ρ p ε α (η b) * bondPartialDeriv g b η e := cc.mul cpg
  rw [ballCovariance_eq hd cg ch1, ballCovariance_eq hd cg ch2, ballCovariance_eq hd cH ch3]
  simp only [hpart] at hs
  have e1 : (fun η => ((g η - mg) * bondPartialDeriv H b η e + (H η - mH) * bondPartialDeriv g b η e) *
      cutCoefficient ρ p ε α (η b)) = fun η => (g η - mg) * (cutCoefficient ρ p ε α (η b) * bondPartialDeriv H b η e) +
        (H η - mH) * (cutCoefficient ρ p ε α (η b) * bondPartialDeriv g b η e) := by
    funext η
    ring
  have e2 : (fun η => (g η - mg) * (H η - mH) * byPartsTerm ρ p ε α Ψ b e η) =
      fun η => (g η - mg) * ((H η - mH) * byPartsTerm ρ p ε α Ψ b e η) := by
    funext η
    ring
  rw [e1, e2] at hs
  rw [ballExpectation_add hd (f := fun η => (g η - mg) * (cutCoefficient ρ p ε α (η b) * bondPartialDeriv H b η e))
    (g := fun η => (H η - mH) * (cutCoefficient ρ p ε α (η b) * bondPartialDeriv g b η e))
    ((cg.sub continuous_const).mul ch1) ((cH.sub continuous_const).mul ch3)] at hs
  linarith
theorem tendsto_ballExpectation_levelStep (hR : CutoffFactorIsRadialCutoff) (hρ : 0 < ρ) (hp : IsCutoff ρ p)
    (hd : IsCutoffMeasureData ρ (extendedCutoff ρ p) Ψ) (b : ι) {G : BondField ι → ℝ} (hG : Continuous G) :
    Tendsto (fun n : ℕ => ballExpectation (extendedCutoff ρ p) Ψ
      (fun η => G η * levelStep ρ p (1 / ((n : ℝ) + 1)) ‖η b‖)) atTop
      (𝓝 (ballExpectation (extendedCutoff ρ p) Ψ G)) := by
  simp only [ballExpectation_def]
  apply Tendsto.div_const
  have hϱ := (ballDensity_contDiff hd).continuous
  have hbound : Integrable fun η => |G η * ballDensity (extendedCutoff ρ p) Ψ η| :=
    (integrable_mul_ballDensity hd hG).abs
  apply tendsto_integral_of_dominated_convergence
    (fun η => |G η * ballDensity (extendedCutoff ρ p) Ψ η|)
  · intro n
    have ct : Continuous fun η : BondField ι => levelStep ρ p (1 / ((n : ℝ) + 1)) ‖η b‖ :=
      (levelStep_norm_contDiff hR hρ hp).continuous.comp (continuous_apply b)
    exact ((hG.mul ct).mul hϱ).aestronglyMeasurable
  · exact hbound
  · intro n
    filter_upwards with η
    have h0 := levelStep_nonneg (ρ := ρ) (p := p) (ε := 1 / ((n : ℝ) + 1)) ‖η b‖
    have h1 := levelStep_le_one (ρ := ρ) (p := p) (ε := 1 / ((n : ℝ) + 1)) ‖η b‖
    rw [Real.norm_eq_abs]
    have e : G η * levelStep ρ p (1 / ((n : ℝ) + 1)) ‖η b‖ * ballDensity (extendedCutoff ρ p) Ψ η =
        levelStep ρ p (1 / ((n : ℝ) + 1)) ‖η b‖ * (G η * ballDensity (extendedCutoff ρ p) Ψ η) := by ring
    rw [e, abs_mul, abs_of_nonneg h0]
    exact mul_le_of_le_one_left (abs_nonneg _) h1
  · filter_upwards with η
    by_cases hη : InOpenBalls ρ η
    · have hr : 0 < extendedCutoff ρ p ‖η b‖ := extendedCutoff_pos hR hρ hp (norm_nonneg _) (hη b)
      have hev : ∀ᶠ n : ℕ in atTop, levelStep ρ p (1 / ((n : ℝ) + 1)) ‖η b‖ = 1 := by
        obtain ⟨N, hN⟩ := exists_nat_gt (2 / extendedCutoff ρ p ‖η b‖)
        filter_upwards [eventually_ge_atTop N] with n hn
        apply smoothStep_of_two_le
        have hn' : (N : ℝ) ≤ n := by exact_mod_cast hn
        have h2 : 2 / extendedCutoff ρ p ‖η b‖ ≤ (n : ℝ) + 1 := by linarith
        rw [div_le_iff₀ hr] at h2
        rw [div_div_eq_mul_div, div_one]
        linarith
      have : (fun n : ℕ => G η * levelStep ρ p (1 / ((n : ℝ) + 1)) ‖η b‖ *
          ballDensity (extendedCutoff ρ p) Ψ η) =ᶠ[atTop]
          fun _ => G η * ballDensity (extendedCutoff ρ p) Ψ η := by
        filter_upwards [hev] with n hn
        rw [hn, mul_one]
      exact (tendsto_const_nhds).congr' this.symm
    · simp [ballDensity_eq_zero hd η hη]
end YangMills.Construction.ColdStepAtMirrorFrames.ThirdDerivative
end
noncomputable section
open MeasureTheory Set Filter Topology
namespace YangMills.Construction.ColdStepAtMirrorFrames.ThirdDerivative
variable {ι : Type} [Fintype ι] [DecidableEq ι]
variable {ρ : ℝ} {p : ℝ → ℝ} {Ψ : BondField ι → ℝ} {ε : ℝ} {α : BondVector → ℝ} {e : BondVector}
theorem radialWeightProd_cutoffFactor (ρ : ℝ) (p : ℝ → ℝ) :
    radialWeightProd (ι := ι) (cutoffFactor ρ p) = radialWeightProd (extendedCutoff ρ p) := by
  funext η
  simp [radialWeightProd, extendedCutoff]
theorem ballCovariance_cutoffFactor (ρ : ℝ) (p : ℝ → ℝ) (Ψ f g : BondField ι → ℝ) :
    ballCovariance (cutoffFactor ρ p) Ψ f g = ballCovariance (extendedCutoff ρ p) Ψ f g := by
  simp only [ballCovariance, ballExpectation, ballDensity, radialWeightProd_cutoffFactor]
theorem ballL2Norm_cutoffFactor (ρ : ℝ) (p : ℝ → ℝ) (Ψ h : BondField ι → ℝ) :
    ballL2Norm (cutoffFactor ρ p) Ψ h = ballL2Norm (extendedCutoff ρ p) Ψ h := by
  simp only [ballL2Norm, ballExpectation, ballDensity, radialWeightProd_cutoffFactor]
theorem ballL2Norm_abs (Ψ h : BondField ι → ℝ) (r : ℝ → ℝ) :
    ballL2Norm r Ψ (fun η => |h η|) = ballL2Norm r Ψ h := by
  simp only [ballL2Norm, sq_abs]
theorem inOpenBalls_zero (hρ : 0 < ρ) : InOpenBalls ρ (0 : BondField ι) := fun b => by simpa using hρ
theorem abs_ballCovariance_le_of_sup (hCov : BallCovarianceBound) {m κ : ℝ} {d : ι → ι → ℝ}
    {K : ι → ι → ℝ} (hρ : 0 < ρ) (hm : 0 < m) (hκ : 0 ≤ κ) (hp : IsCutoff ρ p)
    (hdist : IsPseudoMetricOnBonds d) (hΨ : IsUniformlyConvexDecaying ρ m κ d Ψ K)
    (hd : IsCutoffMeasureData ρ (extendedCutoff ρ p) Ψ) {f h : BondField ι → ℝ} (hf : ContDiff ℝ 1 f)
    (hh : ContDiff ℝ 1 h) {Af Bh : ι → ℝ}
    (hA : ∀ b η, InOpenBalls ρ η → bondGradNorm f b η ≤ Af b)
    (hB : ∀ b, ballL2Norm (extendedCutoff ρ p) Ψ (bondGradNorm h b) ≤ Bh b) :
    |ballCovariance (extendedCutoff ρ p) Ψ f h| ≤
      m⁻¹ * ∑ b, ∑ b', Af b * Real.exp (-(κ * d b b')) * Bh b' := by
  have h0 := hCov ι ρ m κ d Ψ K p hρ hm hκ hp hdist hΨ f h hf hh
  rw [ballCovariance_cutoffFactor] at h0
  refine h0.trans (mul_le_mul_of_nonneg_left ?_ (inv_nonneg.mpr hm.le))
  apply Finset.sum_le_sum
  intro b _
  apply Finset.sum_le_sum
  intro b' _
  have hA0 : 0 ≤ Af b := (bondGradNorm_nonneg f b 0).trans (hA b 0 (inOpenBalls_zero hρ))
  rw [ballL2Norm_cutoffFactor, ballL2Norm_cutoffFactor]
  have n1 : ballL2Norm (extendedCutoff ρ p) Ψ (bondGradNorm f b) ≤ Af b :=
    ballL2Norm_le_const hd (bondGradNorm_continuous hf b) hA0 fun η hη => by
      rw [abs_of_nonneg (bondGradNorm_nonneg _ _ _)]
      exact hA b η hη
  have n2 := hB b'
  exact mul_le_mul (mul_le_mul_of_nonneg_right n1 (Real.exp_pos _).le) n2 (ballL2Norm_nonneg _)
    (by positivity)
def rimBound (ρ : ℝ) (p : ℝ → ℝ) (c ε u : ℝ) : ℝ :=
  c * (slopePower ρ p (ε / 2) 0 u + slopePower ρ p (ε / 2) 1 u + slopePower ρ p (ε / 2) 2 u)
theorem rimBound_continuous (hR : CutoffFactorIsRadialCutoff) (hρ : 0 < ρ) (hp : IsCutoff ρ p) (hε : 0 < ε)
    (c : ℝ) : Continuous (rimBound ρ p c ε) := by
  have h2 : 0 < ε / 2 := by positivity
  unfold rimBound
  exact continuous_const.mul (((slopePower_continuous hR hρ hp h2 0).add
    (slopePower_continuous hR hρ hp h2 1)).add (slopePower_continuous hR hρ hp h2 2))
theorem rimBound_nonneg (hρ : 0 < ρ) (hp : IsCutoff ρ p) {c u : ℝ} (hc : 0 ≤ c) (hu : u < ρ) :
    0 ≤ rimBound ρ p c ε u :=
  mul_nonneg hc (add_nonneg (add_nonneg (slopePower_nonneg hρ hp 0 hu) (slopePower_nonneg hρ hp 1 hu))
    (slopePower_nonneg hρ hp 2 hu))
structure RimBoundConst (ρ : ℝ) (p : ℝ → ℝ) (c : ℝ) : Prop where
  one_le : 1 ≤ c
  bounds : ∀ (ε u : ℝ), 0 < ε → 0 ≤ u → u < ρ → 0 ≤ extendedCutoff ρ p u →
      |levelStepDeriv ρ p ε u| ≤ rimBound ρ p c ε u ∧ u * |levelRatio ρ p ε u| ≤ rimBound ρ p c ε u ∧
      |levelRatio ρ p ε u| ≤ rimBound ρ p c ε u ∧ u * |levelRatioDeriv ρ p ε u| ≤ rimBound ρ p c ε u
theorem abs_inner_le_norm_of_unit (v : BondVector) (he : ‖e‖ = 1) : |inner ℝ v e| ≤ ‖v‖ := by
  have := abs_real_inner_le_norm v e
  rwa [he, mul_one] at this
theorem abs_fderiv_apply_le {N : ℝ} {v : BondVector} (he : ‖e‖ = 1) (h : ‖fderiv ℝ α v‖ ≤ N) :
    |fderiv ℝ α v e| ≤ N := by
  have := (fderiv ℝ α v).le_opNorm e
  rw [he, mul_one, Real.norm_eq_abs] at this
  exact this.trans h
theorem norm_fderiv_fderiv_apply_le (hα : ContDiff ℝ 2 α) {N : ℝ} {v : BondVector} (he : ‖e‖ = 1) (hN : 0 ≤ N)
    (h : ‖fderiv ℝ (fderiv ℝ α) v‖ ≤ N) : ‖fderiv ℝ (fun w => fderiv ℝ α w e) v‖ ≤ N := by
  have hd : DifferentiableAt ℝ (fderiv ℝ α) v :=
    ((hα.fderiv_right (m := 1) (by norm_num)).differentiable (by norm_num)) v
  have h1 : fderiv ℝ (fun w => fderiv ℝ α w e) v =
      (ContinuousLinearMap.apply ℝ ℝ e).comp (fderiv ℝ (fderiv ℝ α) v) :=
    ((ContinuousLinearMap.apply ℝ ℝ e).hasFDerivAt.comp v hd.hasFDerivAt).fderiv
  rw [h1]
  apply ContinuousLinearMap.opNorm_le_bound _ hN
  intro w
  have a1 := (fderiv ℝ (fderiv ℝ α) v w).le_opNorm e
  have a2 := (fderiv ℝ (fderiv ℝ α) v).le_opNorm w
  rw [he, mul_one] at a1
  simp only [ContinuousLinearMap.comp_apply, ContinuousLinearMap.apply_apply]
  have := mul_le_mul_of_nonneg_right h (norm_nonneg w)
  linarith
theorem local_term_bounds (hR : CutoffFactorIsRadialCutoff) (hρ : 0 < ρ) (hp : IsCutoff ρ p) {c : ℝ}
    (hc : RimBoundConst ρ p c) (hε : 0 < ε) (hα : ContDiff ℝ 2 α) (he : ‖e‖ = 1) {N : ℝ} (hN : 0 ≤ N)
    {v : BondVector} (hv : ‖v‖ < ρ) (h0 : |α v| ≤ N) (h1 : ‖fderiv ℝ α v‖ ≤ N)
    (h2 : ‖fderiv ℝ (fderiv ℝ α) v‖ ≤ N) :
    |cutCoefficient ρ p ε α v| ≤ N ∧ ‖fderiv ℝ (cutCoefficient ρ p ε α) v‖ ≤ N * (1 + rimBound ρ p c ε ‖v‖) ∧
      |localTerm ρ p ε α e v| ≤ N * (1 + rimBound ρ p c ε ‖v‖) ∧
      ‖fderiv ℝ (localTerm ρ p ε α e) v‖ ≤ 4 * N * (1 + rimBound ρ p c ε ‖v‖) := by
  have hr := extendedCutoff_nonneg hR hρ hp ‖v‖
  obtain ⟨b1, b2, b3, b4⟩ := hc.bounds ε ‖v‖ hε (norm_nonneg _) hv hr
  have hO : 0 ≤ rimBound ρ p c ε ‖v‖ := rimBound_nonneg hρ hp (by linarith [hc.one_le]) hv
  set O := rimBound ρ p c ε ‖v‖ with hOdef
  have t0 := levelStep_nonneg (ρ := ρ) (p := p) (ε := ε) ‖v‖
  have t1 := levelStep_le_one (ρ := ρ) (p := p) (ε := ε) ‖v‖
  set T := levelStep ρ p ε ‖v‖ with hT
  have hip := abs_inner_le_norm_of_unit (e := e) v he
  have hda := abs_fderiv_apply_le he h1
  have dT : ‖fderiv ℝ (fun v : BondVector => levelStep ρ p ε ‖v‖) v‖ ≤ O :=
    (norm_radialFn_fderiv_le (levelStep_hasDerivAt hR hρ hp hε) (by positivity : 0 < 5 * ρ / 8)
      (fun u hu => levelStep_inner hρ hp hu) v).trans b1
  have dL : ‖fderiv ℝ (fun v : BondVector => levelRatio ρ p ε ‖v‖) v‖ ≤ |levelRatioDeriv ρ p ε ‖v‖| :=
    norm_radialFn_fderiv_le (levelRatio_hasDerivAt hR hρ hp hε) (by positivity : 0 < 5 * ρ / 8)
      (fun u hu => by
        rw [levelRatio_inner hρ hp hu, levelRatio_inner hρ hp (by positivity : (0 : ℝ) < 5 * ρ / 8)]) v
  have hTa : |T| = T := abs_of_nonneg t0
  have hα1 := ((hα.of_le (by norm_num : (1 : WithTop ℕ∞) ≤ 2)).differentiable (by norm_num) v).hasFDerivAt
  have hT1 := (((levelStep_norm_contDiff (ε := ε) hR hρ hp).differentiable (by norm_num)) v).hasFDerivAt
  have hD1 := (((fderiv_apply_contDiff hα e).differentiable (by norm_num)) v).hasFDerivAt
  have hL1 := (((levelRatio_norm_contDiff (ε := ε) hR hρ hp hε).differentiable (by norm_num)) v).hasFDerivAt
  have hI1 := (((inner_left_contDiff e).differentiable (by norm_num)) v).hasFDerivAt
  have dI : ‖fderiv ℝ (fun v : BondVector => inner ℝ v e) v‖ ≤ 1 := by
    have e1 : (fun v : BondVector => (inner ℝ v e : ℝ)) = fun v => innerSL ℝ e v := by
      funext w
      rw [innerSL_apply_apply, real_inner_comm]
    rw [e1, ContinuousLinearMap.fderiv]
    have := innerSL_apply_norm (𝕜 := ℝ) e
    rw [he] at this
    exact this.le
  refine ⟨?_, ?_, ?_, ?_⟩
  · simp only [cutCoefficient, abs_mul]
    rw [← hT, hTa]
    nlinarith [abs_nonneg (α v)]
  · have e1 : fderiv ℝ (cutCoefficient ρ p ε α) v = _ := (hα1.mul hT1).fderiv
    rw [e1]
    refine (_root_.norm_add_le _ _).trans ?_
    rw [norm_smul, norm_smul, Real.norm_eq_abs, Real.norm_eq_abs, ← hT, hTa]
    have a1 := mul_le_mul h0 dT (norm_nonneg _) hN
    have a2 := mul_le_mul t1 h1 (norm_nonneg _) zero_le_one
    nlinarith
  · simp only [localTerm]
    rw [← hT]
    refine (abs_add_le _ _).trans ?_
    rw [abs_neg, abs_mul, abs_mul, abs_mul, hTa]
    have a1 := mul_le_mul t1 hda (abs_nonneg _) zero_le_one
    have a2 : |levelRatio ρ p ε ‖v‖| * |inner ℝ v e| ≤ O :=
      (mul_le_mul_of_nonneg_left hip (abs_nonneg _)).trans (by linarith)
    have a3 := mul_le_mul h0 a2 (by positivity) hN
    nlinarith
  · have e1 : fderiv ℝ (localTerm ρ p ε α e) v = _ :=
      (((hT1.mul hD1).neg).add (hα1.mul (hL1.mul hI1))).fderiv
    rw [e1]
    have n1 := norm_fderiv_fderiv_apply_le hα he hN h2
    refine (_root_.norm_add_le _ _).trans ?_
    rw [norm_neg]
    simp only [Pi.mul_apply]
    have p1 : ‖levelStep ρ p ε ‖v‖ • fderiv ℝ (fun w => fderiv ℝ α w e) v +
        fderiv ℝ α v e • fderiv ℝ (fun v : BondVector => levelStep ρ p ε ‖v‖) v‖ ≤ N + N * O := by
      refine (_root_.norm_add_le _ _).trans ?_
      rw [norm_smul, norm_smul, Real.norm_eq_abs, Real.norm_eq_abs, ← hT, hTa]
      have a1 := mul_le_mul t1 n1 (norm_nonneg _) zero_le_one
      have a2 := mul_le_mul hda dT (norm_nonneg _) hN
      linarith
    have p2 : ‖α v • (levelRatio ρ p ε ‖v‖ • fderiv ℝ (fun v : BondVector => inner ℝ v e) v +
          inner ℝ v e • fderiv ℝ (fun v : BondVector => levelRatio ρ p ε ‖v‖) v) +
        (levelRatio ρ p ε ‖v‖ * inner ℝ v e) • fderiv ℝ α v‖ ≤ N * O + N * O + N * O := by
      refine (_root_.norm_add_le _ _).trans ?_
      rw [norm_smul, norm_smul, Real.norm_eq_abs, Real.norm_eq_abs, abs_mul]
      have q1 : ‖levelRatio ρ p ε ‖v‖ • fderiv ℝ (fun v : BondVector => inner ℝ v e) v +
          inner ℝ v e • fderiv ℝ (fun v : BondVector => levelRatio ρ p ε ‖v‖) v‖ ≤ O + O := by
        refine (_root_.norm_add_le _ _).trans ?_
        rw [norm_smul, norm_smul, Real.norm_eq_abs, Real.norm_eq_abs]
        have a1 := mul_le_mul b3 dI (norm_nonneg _) hO
        have a2 : |inner ℝ v e| * ‖fderiv ℝ (fun v : BondVector => levelRatio ρ p ε ‖v‖) v‖ ≤ O :=
          (mul_le_mul hip dL (norm_nonneg _) (norm_nonneg _)).trans b4
        linarith
      have a3 := mul_le_mul h0 q1 (norm_nonneg _) hN
      have a4 : |levelRatio ρ p ε ‖v‖| * |inner ℝ v e| * ‖fderiv ℝ α v‖ ≤ O * N := by
        have : |levelRatio ρ p ε ‖v‖| * |inner ℝ v e| ≤ O :=
          (mul_le_mul_of_nonneg_left hip (abs_nonneg _)).trans (by linarith)
        exact mul_le_mul this h1 (norm_nonneg _) hO
      nlinarith
    linarith
end YangMills.Construction.ColdStepAtMirrorFrames.ThirdDerivative
end
noncomputable section
open MeasureTheory Set Filter Topology
namespace YangMills.Construction.ColdStepAtMirrorFrames.ThirdDerivative
variable {ι : Type} [Fintype ι] [DecidableEq ι]
structure OneBondHyp (ρ : ℝ) (p : ℝ → ℝ) (m κ : ℝ) (d : ι → ι → ℝ) (Ψ : BondField ι → ℝ)
    (K : ι → ι → ℝ) (b : ι) (e : BondVector) (α : BondVector → ℝ) (N c B s₂ o : ℝ) : Prop where
  pos : 0 < ρ
  cutoff : IsCutoff ρ p
  mass_pos : 0 < m
  rate_nonneg : 0 ≤ κ
  dist : IsPseudoMetricOnBonds d
  convex : IsUniformlyConvexDecaying ρ m κ d Ψ K
  data : IsCutoffMeasureData ρ (extendedCutoff ρ p) Ψ
  unit : ‖e‖ = 1
  coeff_smooth : ContDiff ℝ 2 α
  bound_nonneg : 0 ≤ N
  val_le : ∀ v : BondVector, ‖v‖ < ρ → |α v| ≤ N
  deriv_le : ∀ v : BondVector, ‖v‖ < ρ → ‖fderiv ℝ α v‖ ≤ N
  second_deriv_le : ∀ v : BondVector, ‖v‖ < ρ → ‖fderiv ℝ (fderiv ℝ α) v‖ ≤ N
  rim : RimBoundConst ρ p c
  slope_sup : ∀ η, InOpenBalls ρ η → |bondPartialDeriv Ψ b η e| ≤ B
  slope_l2 : ballL2Norm (extendedCutoff ρ p) Ψ (fun η => bondPartialDeriv Ψ b η e) ≤ s₂
  rim_l2 : ∀ ε, 0 < ε → ballL2Norm (extendedCutoff ρ p) Ψ (fun η => rimBound ρ p c ε ‖η b‖) ≤ o
variable {ρ : ℝ} {p : ℝ → ℝ} {m κ : ℝ} {d : ι → ι → ℝ} {Ψ : BondField ι → ℝ} {K : ι → ι → ℝ}
  {b : ι} {e : BondVector} {α : BondVector → ℝ} {N c B s₂ o : ℝ}
theorem oneBond_kernel_nonneg (h : OneBondHyp ρ p m κ d Ψ K b e α N c B s₂ o) (b' : ι) : 0 ≤ K b b' := by
  have := h.convex.kernel 0 (inOpenBalls_zero h.pos) b b' e e
  rw [h.unit, mul_one, mul_one] at this
  exact (abs_nonneg _).trans this
theorem oneBond_bondGradNorm_partial_le (h : OneBondHyp ρ p m κ d Ψ K b e α N c B s₂ o) (b' : ι)
    (η : BondField ι) (hη : InOpenBalls ρ η) :
    bondGradNorm (fun ζ => bondPartialDeriv Ψ b ζ e) b' η ≤ K b b' := by
  apply bondGradNorm_le (oneBond_kernel_nonneg h b')
  intro e'
  have := h.convex.kernel η hη b b' e e'
  rw [h.unit, mul_one] at this
  exact this
theorem oneBond_slopeSup_nonneg (h : OneBondHyp ρ p m κ d Ψ K b e α N c B s₂ o) : 0 ≤ B :=
  (abs_nonneg _).trans (h.slope_sup 0 (inOpenBalls_zero h.pos))
theorem oneBond_slopeL2_nonneg (h : OneBondHyp ρ p m κ d Ψ K b e α N c B s₂ o) : 0 ≤ s₂ :=
  (ballL2Norm_nonneg _).trans h.slope_l2
theorem oneBond_rimL2_nonneg (h : OneBondHyp ρ p m κ d Ψ K b e α N c B s₂ o) : 0 ≤ o :=
  (ballL2Norm_nonneg _).trans (h.rim_l2 1 one_pos)
variable (hCov : BallCovarianceBound) (hR : CutoffFactorIsRadialCutoff)
include hR in
theorem byPartsTerm_bounds (h : OneBondHyp ρ p m κ d Ψ K b e α N c B s₂ o) {ε : ℝ} (hε : 0 < ε)
    (b' : ι) (η : BondField ι) (hη : InOpenBalls ρ η) :
    |byPartsTerm ρ p ε α Ψ b e η| ≤ N * (|bondPartialDeriv Ψ b η e| + 1 + rimBound ρ p c ε ‖η b‖) ∧
    bondGradNorm (byPartsTerm ρ p ε α Ψ b e) b' η ≤ N * K b b' +
      (if b' = b then N * (B + 4) * (1 + rimBound ρ p c ε ‖η b‖) else 0) := by
  have hρ := h.pos
  have hp := h.cutoff
  have hd := h.data
  have hv := hη b
  obtain ⟨l1, l2, l3, l4⟩ := local_term_bounds hR hρ hp h.rim hε h.coeff_smooth h.unit h.bound_nonneg hv (h.val_le _ hv)
    (h.deriv_le _ hv) (h.second_deriv_le _ hv)
  set O := rimBound ρ p c ε ‖η b‖ with hO
  have hN := h.bound_nonneg
  have hB0 := oneBond_slopeSup_nonneg h
  constructor
  · simp only [byPartsTerm]
    refine (abs_add_le _ _).trans ?_
    rw [abs_mul]
    have := mul_le_mul_of_nonneg_right l1 (abs_nonneg (bondPartialDeriv Ψ b η e))
    nlinarith
  · have hc : ContDiff ℝ 1 (fun ζ : BondField ι => cutCoefficient ρ p ε α (ζ b)) :=
      contDiff_comp_apply (cutCoefficient_contDiff hR hρ hp h.coeff_smooth) b
    have hP : ContDiff ℝ 1 (fun ζ => bondPartialDeriv Ψ b ζ e) :=
      bondPartialDeriv_contDiff (n := 1) (hd.smooth.of_le (by norm_num)) b e
    have hl : ContDiff ℝ 1 (fun ζ : BondField ι => localTerm ρ p ε α e (ζ b)) :=
      contDiff_comp_apply (localTerm_contDiff hR hρ hp hε h.coeff_smooth e) b
    have a1 := bondGradNorm_add_le (hc.mul hP) hl b' η
    have a2 := bondGradNorm_mul_le hc hP b' η
    have a3 := bondGradNorm_comp_apply_le (cutCoefficient_contDiff (ε := ε) hR hρ hp h.coeff_smooth) b b' η
    have a4 := bondGradNorm_comp_apply_le (localTerm_contDiff (ε := ε) hR hρ hp hε h.coeff_smooth e) b b' η
    have a5 := oneBond_bondGradNorm_partial_le h b' η hη
    have a6 := h.slope_sup η hη
    have e0 : bondGradNorm (byPartsTerm ρ p ε α Ψ b e) b' η = bondGradNorm (fun ζ =>
        (fun ζ : BondField ι => cutCoefficient ρ p ε α (ζ b)) ζ * (fun ζ => bondPartialDeriv Ψ b ζ e) ζ +
          (fun ζ : BondField ι => localTerm ρ p ε α e (ζ b)) ζ) b' η := rfl
    rw [e0]
    refine a1.trans ?_
    have t1 : |cutCoefficient ρ p ε α (η b)| * bondGradNorm (fun ζ => bondPartialDeriv Ψ b ζ e) b' η ≤ N * K b b' :=
      mul_le_mul l1 a5 (bondGradNorm_nonneg _ _ _) hN
    by_cases hb : b' = b
    · rw [if_pos hb] at a3 a4 ⊢
      have t2 : |bondPartialDeriv Ψ b η e| * bondGradNorm (fun ζ : BondField ι => cutCoefficient ρ p ε α (ζ b)) b' η ≤
          B * (N * (1 + O)) :=
        mul_le_mul a6 (a3.trans l2) (bondGradNorm_nonneg _ _ _) hB0
      have e1 : N * (B + 4) * (1 + O) = B * (N * (1 + O)) + 4 * N * (1 + O) := by ring
      rw [e1]
      linarith
    · rw [if_neg hb] at a3 a4 ⊢
      have z1 : bondGradNorm (fun ζ : BondField ι => cutCoefficient ρ p ε α (ζ b)) b' η = 0 :=
        le_antisymm a3 (bondGradNorm_nonneg _ _ _)
      rw [z1, mul_zero] at a2
      linarith
include hR in
theorem ballL2Norm_bondGradNorm_centered_mul_le (h : OneBondHyp ρ p m κ d Ψ K b e α N c B s₂ o) {ε : ℝ} (hε : 0 < ε)
    {H : BondField ι → ℝ} (hH : ContDiff ℝ 1 H) {Hd : ι → ℝ} {hv hs : ℝ}
    (hHd : ∀ b' η, InOpenBalls ρ η → bondGradNorm H b' η ≤ Hd b')
    (hhv : ballL2Norm (extendedCutoff ρ p) Ψ (fun η => H η - ballExpectation (extendedCutoff ρ p) Ψ H) ≤ hv)
    (hhs : ∀ η, InOpenBalls ρ η → |H η - ballExpectation (extendedCutoff ρ p) Ψ H| ≤ hs) (b' : ι) :
    ballL2Norm (extendedCutoff ρ p) Ψ
        (bondGradNorm (fun η => (H η - ballExpectation (extendedCutoff ρ p) Ψ H) * byPartsTerm ρ p ε α Ψ b e η) b') ≤
      N * K b b' * hv + (if b' = b then N * (B + 4) * (hv + hs * o) else 0) +
        Hd b' * (N * (s₂ + 1 + o)) := by
  have hρ := h.pos
  have hp := h.cutoff
  have hd := h.data
  have hN := h.bound_nonneg
  set mH := ballExpectation (extendedCutoff ρ p) Ψ H with hmH
  have hS := byPartsTerm_contDiff (ε := ε) hR hρ hp hε h.coeff_smooth hd.smooth b e
  have hHt : ContDiff ℝ 1 (fun η => H η - mH) := hH.sub contDiff_const
  have hHS : ContDiff ℝ 1 (fun η => (H η - mH) * byPartsTerm ρ p ε α Ψ b e η) := hHt.mul hS
  have cH : Continuous (fun η => H η - mH) := hHt.continuous
  have cP : Continuous (fun η => bondPartialDeriv Ψ b η e) :=
    (bondPartialDeriv_contDiff (n := 1) (hd.smooth.of_le (by norm_num)) b e).continuous
  have cO : Continuous (fun η : BondField ι => rimBound ρ p c ε ‖η b‖) :=
    (rimBound_continuous hR hρ hp hε c).comp (continuous_apply b).norm
  have hs0 : 0 ≤ hs := (abs_nonneg _).trans (hhs 0 (inOpenBalls_zero hρ))
  have hHd0 : 0 ≤ Hd b' := (bondGradNorm_nonneg H b' 0).trans (hHd b' 0 (inOpenBalls_zero hρ))
  have hK0 := oneBond_kernel_nonneg h b'
  have hB0 := oneBond_slopeSup_nonneg h
  set F : BondField ι → ℝ := fun η =>
    N * K b b' * |H η - mH| +
      (if b' = b then N * (B + 4) * (|H η - mH| + hs * rimBound ρ p c ε ‖η b‖) else 0) +
      Hd b' * (N * (|bondPartialDeriv Ψ b η e| + 1 + rimBound ρ p c ε ‖η b‖)) with hF
  have cF : Continuous F := by
    have c2 : Continuous fun η => |bondPartialDeriv Ψ b η e| := cP.abs
    simp only [hF]
    by_cases hb : b' = b
    · simp only [if_pos hb]
      fun_prop
    · simp only [if_neg hb]
      fun_prop
  have hle : ∀ η, InOpenBalls ρ η →
      |bondGradNorm (fun η => (H η - mH) * byPartsTerm ρ p ε α Ψ b e η) b' η| ≤ |F η| := by
    intro η hη
    rw [abs_of_nonneg (bondGradNorm_nonneg _ _ _)]
    obtain ⟨s1, s2⟩ := byPartsTerm_bounds hR h hε b' η hη
    have a1 := bondGradNorm_mul_le hHt hS b' η
    have a2 : bondGradNorm (fun ζ => H ζ - mH) b' η = bondGradNorm H b' η := bondGradNorm_sub_const mH b' η
    rw [a2] at a1
    have a3 := hHd b' η hη
    have a4 := hhs η hη
    have hO0 : 0 ≤ rimBound ρ p c ε ‖η b‖ := rimBound_nonneg hρ hp (by linarith [h.rim.one_le]) (hη b)
    set O := rimBound ρ p c ε ‖η b‖ with hO
    set h1 := |H η - mH| with hh1
    have h10 : 0 ≤ h1 := abs_nonneg _
    have t1 : |byPartsTerm ρ p ε α Ψ b e η| * bondGradNorm H b' η ≤
        Hd b' * (N * (|bondPartialDeriv Ψ b η e| + 1 + O)) := by
      rw [mul_comm]
      exact mul_le_mul a3 s1 (abs_nonneg _) hHd0
    have t2 : h1 * bondGradNorm (byPartsTerm ρ p ε α Ψ b e) b' η ≤
        N * K b b' * h1 + (if b' = b then N * (B + 4) * (h1 + hs * O) else 0) := by
      refine (mul_le_mul_of_nonneg_left s2 h10).trans ?_
      by_cases hb : b' = b
      · simp only [if_pos hb]
        have : h1 * (N * (B + 4) * (1 + O)) ≤ N * (B + 4) * (h1 + hs * O) := by
          have w : 0 ≤ N * (B + 4) := by positivity
          have : h1 * O ≤ hs * O := mul_le_mul_of_nonneg_right a4 hO0
          nlinarith
        nlinarith
      · simp only [if_neg hb]
        linarith
    have hFη : 0 ≤ F η := by
      simp only [hF]
      have u1 : 0 ≤ N * K b b' * h1 := by positivity
      have u2 : 0 ≤ (if b' = b then N * (B + 4) * (h1 + hs * O) else 0) := by
        split_ifs <;> positivity
      have u3 : 0 ≤ Hd b' * (N * (|bondPartialDeriv Ψ b η e| + 1 + O)) := by positivity
      linarith
    rw [abs_of_nonneg hFη]
    simp only [hF]
    linarith
  have n0 := ballL2Norm_le_of_abs_le hd (bondGradNorm_continuous hHS b') cF hle
  refine n0.trans ?_
  have cA : Continuous fun η => |H η - mH| := cH.abs
  have nA : ballL2Norm (extendedCutoff ρ p) Ψ (fun η => |H η - mH|) ≤ hv := by
    rw [ballL2Norm_abs]
    exact hhv
  have nO := h.rim_l2 ε hε
  have nP : ballL2Norm (extendedCutoff ρ p) Ψ (fun η => |bondPartialDeriv Ψ b η e|) ≤ s₂ := by
    rw [ballL2Norm_abs]
    exact h.slope_l2
  have nP3 : ballL2Norm (extendedCutoff ρ p) Ψ (fun η => |bondPartialDeriv Ψ b η e| + 1 + rimBound ρ p c ε ‖η b‖) ≤
      s₂ + 1 + o := by
    refine (ballL2Norm_add_le hd (f := fun η => |bondPartialDeriv Ψ b η e| + 1) (g := fun η => rimBound ρ p c ε ‖η b‖)
      (cP.abs.add continuous_const) cO).trans ?_
    have := ballL2Norm_add_le hd (f := fun η => |bondPartialDeriv Ψ b η e|) (g := fun _ => (1 : ℝ)) cP.abs
      continuous_const
    rw [ballL2Norm_const hd zero_le_one] at this
    linarith
  have nL : ballL2Norm (extendedCutoff ρ p) Ψ (fun η => N * K b b' * |H η - mH|) ≤ N * K b b' * hv := by
    rw [ballL2Norm_const_mul hd, abs_of_nonneg (by positivity)]
    exact mul_le_mul_of_nonneg_left nA (by positivity)
  have nR : ballL2Norm (extendedCutoff ρ p) Ψ
      (fun η => Hd b' * (N * (|bondPartialDeriv Ψ b η e| + 1 + rimBound ρ p c ε ‖η b‖))) ≤
      Hd b' * (N * (s₂ + 1 + o)) := by
    rw [ballL2Norm_const_mul hd, ballL2Norm_const_mul hd, abs_of_nonneg hHd0, abs_of_nonneg hN]
    exact mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left nP3 hN) hHd0
  have cR : Continuous fun η => Hd b' * (N * (|bondPartialDeriv Ψ b η e| + 1 + rimBound ρ p c ε ‖η b‖)) := by
    have c2 : Continuous fun η => |bondPartialDeriv Ψ b η e| := cP.abs
    fun_prop
  by_cases hb : b' = b
  · simp only [hF, if_pos hb]
    have nM : ballL2Norm (extendedCutoff ρ p) Ψ
        (fun η => N * (B + 4) * (|H η - mH| + hs * rimBound ρ p c ε ‖η b‖)) ≤
        N * (B + 4) * (hv + hs * o) := by
      rw [ballL2Norm_const_mul hd, abs_of_nonneg (by positivity)]
      apply mul_le_mul_of_nonneg_left _ (by positivity)
      refine (ballL2Norm_add_le hd (f := fun η => |H η - mH|)
        (g := fun η => hs * rimBound ρ p c ε ‖η b‖) cA (continuous_const.mul cO)).trans ?_
      rw [ballL2Norm_const_mul hd, abs_of_nonneg hs0]
      have := mul_le_mul_of_nonneg_left nO hs0
      linarith
    have cL : Continuous fun η => N * K b b' * |H η - mH| := continuous_const.mul cA
    have cM : Continuous fun η => N * (B + 4) * (|H η - mH| + hs * rimBound ρ p c ε ‖η b‖) :=
      continuous_const.mul (cA.add (continuous_const.mul cO))
    have cLM : Continuous fun η => N * K b b' * |H η - mH| +
        N * (B + 4) * (|H η - mH| + hs * rimBound ρ p c ε ‖η b‖) := cL.add cM
    refine (ballL2Norm_add_le hd cLM cR).trans ?_
    have := ballL2Norm_add_le hd cL cM
    linarith
  · simp only [hF, if_neg hb, add_zero]
    have cL : Continuous fun η => N * K b b' * |H η - mH| := continuous_const.mul cA
    refine (ballL2Norm_add_le hd cL cR).trans ?_
    linarith
include hR in
theorem ballL2Norm_bondGradNorm_cutCoefficient_le (h : OneBondHyp ρ p m κ d Ψ K b e α N c B s₂ o) {ε : ℝ} (hε : 0 < ε)
    {g : BondField ι → ℝ} (hg : ContDiff ℝ 2 g) {A Ge : ι → ℝ}
    (hA : ∀ b' η, InOpenBalls ρ η → bondGradNorm g b' η ≤ A b')
    (hGe : ∀ b' η, InOpenBalls ρ η → bondGradNorm (fun ζ => bondPartialDeriv g b ζ e) b' η ≤ Ge b') (b' : ι) :
    ballL2Norm (extendedCutoff ρ p) Ψ
        (bondGradNorm (fun η => cutCoefficient ρ p ε α (η b) * bondPartialDeriv g b η e) b') ≤
      N * Ge b' + (if b' = b then A b * (N * (1 + o)) else 0) := by
  have hρ := h.pos
  have hp := h.cutoff
  have hd := h.data
  have hN := h.bound_nonneg
  have hc : ContDiff ℝ 1 (fun ζ : BondField ι => cutCoefficient ρ p ε α (ζ b)) :=
    contDiff_comp_apply (cutCoefficient_contDiff hR hρ hp h.coeff_smooth) b
  have hP : ContDiff ℝ 1 (fun ζ => bondPartialDeriv g b ζ e) :=
    bondPartialDeriv_contDiff (n := 1) (by rw [one_add_one_eq_two]; exact hg) b e
  have hcP : ContDiff ℝ 1 (fun η => cutCoefficient ρ p ε α (η b) * bondPartialDeriv g b η e) := hc.mul hP
  have cO : Continuous (fun η : BondField ι => rimBound ρ p c ε ‖η b‖) :=
    (rimBound_continuous hR hρ hp hε c).comp (continuous_apply b).norm
  have hA0 : 0 ≤ A b := (bondGradNorm_nonneg g b 0).trans (hA b 0 (inOpenBalls_zero hρ))
  have hG0 : 0 ≤ Ge b' := (bondGradNorm_nonneg _ b' 0).trans (hGe b' 0 (inOpenBalls_zero hρ))
  set F : BondField ι → ℝ := fun η =>
    N * Ge b' + (if b' = b then A b * (N * (1 + rimBound ρ p c ε ‖η b‖)) else 0) with hF
  have cF : Continuous F := by
    simp only [hF]
    by_cases hb : b' = b
    · simp only [if_pos hb]
      fun_prop
    · simp only [if_neg hb]
      fun_prop
  have hle : ∀ η, InOpenBalls ρ η →
      |bondGradNorm (fun η => cutCoefficient ρ p ε α (η b) * bondPartialDeriv g b η e) b' η| ≤ |F η| := by
    intro η hη
    rw [abs_of_nonneg (bondGradNorm_nonneg _ _ _)]
    have hv := hη b
    obtain ⟨l1, l2, l3, l4⟩ := local_term_bounds hR hρ hp h.rim hε h.coeff_smooth h.unit hN hv (h.val_le _ hv)
      (h.deriv_le _ hv) (h.second_deriv_le _ hv)
    have hO0 : 0 ≤ rimBound ρ p c ε ‖η b‖ := rimBound_nonneg hρ hp (by linarith [h.rim.one_le]) hv
    have a1 := bondGradNorm_mul_le hc hP b' η
    have a3 := bondGradNorm_comp_apply_le (cutCoefficient_contDiff (ε := ε) hR hρ hp h.coeff_smooth) b b' η
    have a5 := hGe b' η hη
    have a6 : |bondPartialDeriv g b η e| ≤ A b := by
      have := abs_fderiv_bondVariation_le g b η e
      rw [h.unit, mul_one] at this
      exact this.trans (hA b η hη)
    have t1 : |cutCoefficient ρ p ε α (η b)| * bondGradNorm (fun ζ => bondPartialDeriv g b ζ e) b' η ≤ N * Ge b' :=
      mul_le_mul l1 a5 (bondGradNorm_nonneg _ _ _) hN
    have hFη : 0 ≤ F η := by
      simp only [hF]
      have u1 : 0 ≤ N * Ge b' := by positivity
      have u2 : 0 ≤ (if b' = b then A b * (N * (1 + rimBound ρ p c ε ‖η b‖)) else 0) := by
        split_ifs <;> positivity
      linarith
    rw [abs_of_nonneg hFη]
    simp only [hF]
    refine a1.trans ?_
    by_cases hb : b' = b
    · rw [if_pos hb] at a3 ⊢
      have t2 : |bondPartialDeriv g b η e| * bondGradNorm (fun ζ : BondField ι => cutCoefficient ρ p ε α (ζ b)) b' η ≤
          A b * (N * (1 + rimBound ρ p c ε ‖η b‖)) :=
        mul_le_mul a6 (a3.trans l2) (bondGradNorm_nonneg _ _ _) hA0
      linarith
    · rw [if_neg hb] at a3 ⊢
      have z1 : bondGradNorm (fun ζ : BondField ι => cutCoefficient ρ p ε α (ζ b)) b' η = 0 :=
        le_antisymm a3 (bondGradNorm_nonneg _ _ _)
      rw [z1, mul_zero]
      linarith
  refine (ballL2Norm_le_of_abs_le hd (bondGradNorm_continuous hcP b') cF hle).trans ?_
  have nG : ballL2Norm (extendedCutoff ρ p) Ψ (fun _ : BondField ι => N * Ge b') = N * Ge b' :=
    ballL2Norm_const hd (by positivity)
  by_cases hb : b' = b
  · simp only [hF, if_pos hb]
    have c2 : Continuous fun η : BondField ι => A b * (N * (1 + rimBound ρ p c ε ‖η b‖)) := by
      fun_prop
    refine (ballL2Norm_add_le hd continuous_const c2).trans ?_
    rw [nG, ballL2Norm_const_mul hd, ballL2Norm_const_mul hd, abs_of_nonneg hA0, abs_of_nonneg hN]
    have n1 : ballL2Norm (extendedCutoff ρ p) Ψ (fun η => 1 + rimBound ρ p c ε ‖η b‖) ≤ 1 + o := by
      refine (ballL2Norm_add_le hd continuous_const cO).trans ?_
      rw [ballL2Norm_const hd zero_le_one]
      linarith [h.rim_l2 ε hε]
    have := mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left n1 hN) hA0
    linarith
  · simp only [hF, if_neg hb, add_zero]
    rw [nG]
include hCov hR in
theorem abs_ballCovariance_bondTerm_le (h : OneBondHyp ρ p m κ d Ψ K b e α N c B s₂ o)
    {g H : BondField ι → ℝ} (hg : ContDiff ℝ 2 g) (hH : ContDiff ℝ 1 H) {A Hd Ge : ι → ℝ}
    {hv hs : ℝ} (hA : ∀ b' η, InOpenBalls ρ η → bondGradNorm g b' η ≤ A b')
    (hHd : ∀ b' η, InOpenBalls ρ η → bondGradNorm H b' η ≤ Hd b')
    (hGe : ∀ b' η, InOpenBalls ρ η → bondGradNorm (fun ζ => bondPartialDeriv g b ζ e) b' η ≤ Ge b')
    (hhv : ballL2Norm (extendedCutoff ρ p) Ψ (fun η => H η - ballExpectation (extendedCutoff ρ p) Ψ H) ≤ hv)
    (hhs : ∀ η, InOpenBalls ρ η → |H η - ballExpectation (extendedCutoff ρ p) Ψ H| ≤ hs) :
    |ballCovariance (extendedCutoff ρ p) Ψ g (fun η => α (η b) * bondPartialDeriv H b η e)| ≤
      m⁻¹ * (∑ b₁, ∑ b₂, A b₁ * Real.exp (-(κ * d b₁ b₂)) *
          (N * K b b₂ * hv + (if b₂ = b then N * (B + 4) * (hv + hs * o) else 0) +
            Hd b₂ * (N * (s₂ + 1 + o)))) +
      m⁻¹ * ∑ b₁, ∑ b₂, Hd b₁ * Real.exp (-(κ * d b₁ b₂)) *
          (N * Ge b₂ + (if b₂ = b then A b * (N * (1 + o)) else 0)) := by
  have hρ := h.pos
  have hp := h.cutoff
  have hd := h.data
  have hg1 : ContDiff ℝ 1 g := hg.of_le (by norm_num)
  have cg := hg1.continuous
  set mg := ballExpectation (extendedCutoff ρ p) Ψ g with hmg
  set mH := ballExpectation (extendedCutoff ρ p) Ψ H with hmH
  set RHS := m⁻¹ * (∑ b₁, ∑ b₂, A b₁ * Real.exp (-(κ * d b₁ b₂)) *
          (N * K b b₂ * hv + (if b₂ = b then N * (B + 4) * (hv + hs * o) else 0) +
            Hd b₂ * (N * (s₂ + 1 + o)))) +
      m⁻¹ * ∑ b₁, ∑ b₂, Hd b₁ * Real.exp (-(κ * d b₁ b₂)) *
          (N * Ge b₂ + (if b₂ = b then A b * (N * (1 + o)) else 0)) with hRHS
  have step : ∀ ε : ℝ, 0 < ε →
      |ballCovariance (extendedCutoff ρ p) Ψ g (fun η => cutCoefficient ρ p ε α (η b) * bondPartialDeriv H b η e)| ≤ RHS := by
    intro ε hε
    rw [ballCovariance_by_parts hR hρ hp hε hd h.coeff_smooth b e hg1 hH]
    have hS := byPartsTerm_contDiff (ε := ε) hR hρ hp hε h.coeff_smooth hd.smooth b e
    have hHS : ContDiff ℝ 1 (fun η => (H η - mH) * byPartsTerm ρ p ε α Ψ b e η) :=
      (hH.sub contDiff_const).mul hS
    have hc : ContDiff ℝ 1 (fun ζ : BondField ι => cutCoefficient ρ p ε α (ζ b)) :=
      contDiff_comp_apply (cutCoefficient_contDiff hR hρ hp h.coeff_smooth) b
    have hP : ContDiff ℝ 1 (fun ζ => bondPartialDeriv g b ζ e) :=
      bondPartialDeriv_contDiff (n := 1) (by rw [one_add_one_eq_two]; exact hg) b e
    have hcP : ContDiff ℝ 1 (fun η => cutCoefficient ρ p ε α (η b) * bondPartialDeriv g b η e) := hc.mul hP
    have t1 := abs_ballCovariance_le_of_sup hCov hρ h.mass_pos h.rate_nonneg hp h.dist h.convex hd hg1 hHS hA
      (fun b₂ => ballL2Norm_bondGradNorm_centered_mul_le hR h hε hH hHd hhv hhs b₂)
    have t2 := abs_ballCovariance_le_of_sup hCov hρ h.mass_pos h.rate_nonneg hp h.dist h.convex hd hH hcP hHd
      (fun b₂ => ballL2Norm_bondGradNorm_cutCoefficient_le hR h hε hg hA hGe b₂)
    refine (abs_sub _ _).trans ?_
    exact add_le_add t1 t2
  have hlim := tendsto_ballExpectation_levelStep hR hρ hp hd b (G := fun η => (g η - mg) * (α (η b) * bondPartialDeriv H b η e))
    ((cg.sub continuous_const).mul
      ((h.coeff_smooth.continuous.comp (continuous_apply b)).mul (bondPartialDeriv_continuous hH b e)))
  have hα0 : Continuous fun η : BondField ι => α (η b) * bondPartialDeriv H b η e :=
    (h.coeff_smooth.continuous.comp (continuous_apply b)).mul (bondPartialDeriv_continuous hH b e)
  have e1 : ballCovariance (extendedCutoff ρ p) Ψ g (fun η => α (η b) * bondPartialDeriv H b η e) =
      ballExpectation (extendedCutoff ρ p) Ψ (fun η => (g η - mg) * (α (η b) * bondPartialDeriv H b η e)) :=
    ballCovariance_eq hd cg hα0
  rw [e1]
  refine le_of_tendsto hlim.abs (Eventually.of_forall fun n => ?_)
  have hε : (0 : ℝ) < 1 / ((n : ℝ) + 1) := by positivity
  have hcc : Continuous fun η => cutCoefficient ρ p (1 / ((n : ℝ) + 1)) α (η b) * bondPartialDeriv H b η e :=
    ((cutCoefficient_contDiff hR hρ hp h.coeff_smooth).continuous.comp (continuous_apply b)).mul
      (bondPartialDeriv_continuous hH b e)
  have := step _ hε
  rw [ballCovariance_eq hd cg hcc] at this
  have e2 : (fun η => (g η - mg) * (α (η b) * bondPartialDeriv H b η e) * levelStep ρ p (1 / ((n : ℝ) + 1)) ‖η b‖) =
      fun η => (g η - ballExpectation (extendedCutoff ρ p) Ψ g) *
        (cutCoefficient ρ p (1 / ((n : ℝ) + 1)) α (η b) * bondPartialDeriv H b η e) := by
    funext η
    simp only [cutCoefficient]
    ring
  rw [e2]
  exact this
end YangMills.Construction.ColdStepAtMirrorFrames.ThirdDerivative
end
noncomputable section
open MeasureTheory Set Filter Topology
namespace YangMills.Construction.ColdStepAtMirrorFrames.ThirdDerivative
variable {ι : Type} [Fintype ι] [DecidableEq ι]
def fieldAlongDeriv (z : ι → BondVector → BondVector) (η : BondField ι) :
    BondField ι →L[ℝ] BondField ι :=
  ContinuousLinearMap.pi fun b => (fderiv ℝ (z b) (η b)).comp (ContinuousLinearMap.proj b)
theorem fieldAlong_contDiff {z : ι → BondVector → BondVector} {n : WithTop ℕ∞}
    (hz : ∀ b, ContDiff ℝ n (z b)) : ContDiff ℝ n (fieldAlong z) :=
  contDiff_pi.2 fun b => (hz b).comp (contDiff_apply ℝ BondVector b)
theorem fieldAlong_hasFDerivAt {z : ι → BondVector → BondVector} (hz : ∀ b, ContDiff ℝ 1 (z b))
    (η : BondField ι) : HasFDerivAt (fieldAlong z) (fieldAlongDeriv z η) η := by
  rw [hasFDerivAt_pi']
  intro b
  have h1 := (((hz b).differentiable (by norm_num)) (η b)).hasFDerivAt
  have h2 := (ContinuousLinearMap.proj (R := ℝ) (φ := fun _ : ι => BondVector) b).hasFDerivAt (x := η)
  have h3 : HasFDerivAt (fun x : BondField ι => z b (x b))
      ((fderiv ℝ (z b) (η b)).comp (ContinuousLinearMap.proj b)) η := h1.comp η h2
  simpa [fieldAlongDeriv, fieldAlong] using h3
theorem fieldAlongDeriv_bondVariation (z : ι → BondVector → BondVector) (η : BondField ι) (b : ι) (e : BondVector) :
    fieldAlongDeriv z η (bondVariation b e) = bondVariation b (fderiv ℝ (z b) (η b) e) := by
  funext b'
  by_cases h : b' = b
  · subst h
    simp [fieldAlongDeriv, bondVariation]
  · simp [fieldAlongDeriv, bondVariation, Pi.single_eq_of_ne h]
theorem eq_sum_bondVariation (u : BondField ι) : u = ∑ b, bondVariation b (u b) := by
  simp [bondVariation, Finset.univ_sum_single]
structure PlaceWeights (wa wq : ι → ℝ) (W : ℝ) : Prop where
  nonneg : ∀ b, 0 ≤ wa b
  le : ∀ b, wa b ≤ wq b
  sum : ∑ b, wq b ≤ W
def IsAdmissible (wa wq u : ι → ℝ) (ψ : ℝ) : Prop := ∀ b, wa b * u b ≤ ψ * wq b
variable {ρ : ℝ} {G : BondField ι → ℝ} {E E₃ W ψ ψ' : ℝ} {wa wq : ι → ℝ}
  {z w : ι → BondVector → BondVector} {u v : ι → ℝ}
theorem fderiv_contDiff_two (h : ContDiff ℝ 3 G) : ContDiff ℝ 2 (fderiv ℝ G) :=
  h.fderiv_right (m := 2) (by norm_num)
theorem fderiv_fderiv_contDiff_one (h : ContDiff ℝ 3 G) : ContDiff ℝ 1 (fderiv ℝ (fderiv ℝ G)) :=
  (fderiv_contDiff_two h).fderiv_right (m := 1) (by norm_num)
theorem secondDerivAlong_contDiff (h : ContDiff ℝ 3 G) (hz : ∀ b, ContDiff ℝ 1 (z b))
    (hw : ∀ b, ContDiff ℝ 1 (w b)) : ContDiff ℝ 1 (secondDerivAlong G z w) :=
  ((fderiv_fderiv_contDiff_one h).clm_apply (fieldAlong_contDiff hz)).clm_apply (fieldAlong_contDiff hw)
theorem derivAlong_contDiff (h : ContDiff ℝ 3 G) (hz : ∀ b, ContDiff ℝ 1 (z b)) : ContDiff ℝ 1 (derivAlong G z) :=
  ((fderiv_contDiff_two h).of_le (by norm_num)).clm_apply (fieldAlong_contDiff hz)
theorem secondDerivAlong_fderiv (h : ContDiff ℝ 3 G) (hz : ∀ b, ContDiff ℝ 1 (z b))
    (hw : ∀ b, ContDiff ℝ 1 (w b)) (η k : BondField ι) :
    fderiv ℝ (secondDerivAlong G z w) η k =
      fderiv ℝ (fderiv ℝ (fderiv ℝ G)) η k (fieldAlong z η) (fieldAlong w η) +
        fderiv ℝ (fderiv ℝ G) η (fieldAlongDeriv z η k) (fieldAlong w η) +
        fderiv ℝ (fderiv ℝ G) η (fieldAlong z η) (fieldAlongDeriv w η k) := by
  have h2 := (((fderiv_fderiv_contDiff_one h).differentiable (by norm_num)) η).hasFDerivAt
  have h3 := (h2.clm_apply (fieldAlong_hasFDerivAt hz η)).clm_apply (fieldAlong_hasFDerivAt hw η)
  have h4 : fderiv ℝ (secondDerivAlong G z w) η = _ := h3.fderiv
  rw [h4]
  simp
  ring
theorem derivAlong_fderiv (h : ContDiff ℝ 3 G) (hz : ∀ b, ContDiff ℝ 1 (z b)) (η k : BondField ι) :
    fderiv ℝ (derivAlong G z) η k = fderiv ℝ (fderiv ℝ G) η k (fieldAlong z η) +
      fderiv ℝ G η (fieldAlongDeriv z η k) := by
  have h2 := ((((fderiv_contDiff_two h).of_le (by norm_num : (1 : WithTop ℕ∞) ≤ 2)).differentiable (by norm_num)) η).hasFDerivAt
  have h3 := h2.clm_apply (fieldAlong_hasFDerivAt hz η)
  have h4 : fderiv ℝ (derivAlong G z) η = _ := h3.fderiv
  rw [h4]
  simp
  ring
theorem sum_weight_mul_le (hw : PlaceWeights wa wq W) (hA : IsAdmissible wa wq u ψ) (hψ : 0 ≤ ψ) : ∑ b, wa b * u b ≤ ψ * W :=
  (Finset.sum_le_sum fun b _ => hA b).trans (by
    rw [← Finset.mul_sum]
    exact mul_le_mul_of_nonneg_left hw.sum hψ)
theorem fieldC1Bound_nonneg (hL : FieldC1Bound ρ z u) (hρ : 0 < ρ) (b : ι) : 0 ≤ u b :=
  (norm_nonneg _).trans (hL.norm_le b 0 (by simpa using hρ))
theorem bilin_eq_sum_bondVariation (A : BondField ι →L[ℝ] BondField ι →L[ℝ] ℝ) (p q : BondField ι) :
    A p q = ∑ b, ∑ b', A (bondVariation b (p b)) (bondVariation b' (q b')) := by apply _root_.YangMills.Construction.CostDerivatives.bilinear_eq_sum_single <;> assumption
theorem abs_secondDerivAlong_le (hJ : ThirdJetBound ρ G E E₃ wa) (hw : PlaceWeights wa wq W) (hE : 0 ≤ E) (hρ : 0 < ρ)
    (hz : FieldC1Bound ρ z u) (hv : FieldC1Bound ρ w v) (hA : IsAdmissible wa wq u ψ) (hB : IsAdmissible wa wq v ψ') (hψ : 0 ≤ ψ)
    (hψ' : 0 ≤ ψ') (η : BondField ι) (hη : InOpenBalls ρ η) :
    |secondDerivAlong G z w η| ≤ E * (ψ * W) * (ψ' * W) := by
  unfold secondDerivAlong
  rw [bilin_eq_sum_bondVariation]
  refine (Finset.abs_sum_le_sum_abs _ _).trans ?_
  have key : ∀ b, |∑ b', fderiv ℝ (fderiv ℝ G) η (bondVariation b (fieldAlong z η b))
        (bondVariation b' (fieldAlong w η b'))| ≤ E * (wa b * u b) * (ψ' * W) := by
    intro b
    refine (Finset.abs_sum_le_sum_abs _ _).trans ?_
    have s2 : ∑ b', |fderiv ℝ (fderiv ℝ G) η (bondVariation b (fieldAlong z η b))
        (bondVariation b' (fieldAlong w η b'))| ≤ ∑ b', E * (wa b * u b) * (wa b' * v b') := by
      apply Finset.sum_le_sum
      intro b' _
      have h1 := hJ.second η hη b b' (fieldAlong z η b) (fieldAlong w η b')
      have n1 : ‖fieldAlong z η b‖ ≤ u b := hz.norm_le b _ (hη b)
      have n2 : ‖fieldAlong w η b'‖ ≤ v b' := hv.norm_le b' _ (hη b')
      have w0 := hw.nonneg b
      have w1 := hw.nonneg b'
      have c0 : 0 ≤ E * wa b * wa b' := by positivity
      have := mul_le_mul_of_nonneg_left (mul_le_mul n1 n2 (norm_nonneg _) (fieldC1Bound_nonneg hz hρ b)) c0
      calc _ ≤ _ := h1
        _ ≤ _ := this
        _ = _ := by ring
    refine s2.trans ?_
    rw [← Finset.mul_sum]
    have := sum_weight_mul_le hw hB hψ'
    have c0 : 0 ≤ E * (wa b * u b) := mul_nonneg hE (mul_nonneg (hw.nonneg b) (fieldC1Bound_nonneg hz hρ b))
    exact mul_le_mul_of_nonneg_left this c0
  refine (Finset.sum_le_sum fun b _ => key b).trans ?_
  have e : ∑ b, E * (wa b * u b) * (ψ' * W) = E * (∑ b, wa b * u b) * (ψ' * W) := by
    rw [Finset.mul_sum, Finset.sum_mul]
  rw [e]
  have h0 := sum_weight_mul_le hw hA hψ
  have hW : 0 ≤ W := (Finset.sum_nonneg fun b _ => (hw.nonneg b).trans (hw.le b)).trans hw.sum
  apply mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left h0 hE) (by positivity)
end YangMills.Construction.ColdStepAtMirrorFrames.ThirdDerivative
end
noncomputable section
open MeasureTheory Set Filter Topology
namespace YangMills.Construction.ColdStepAtMirrorFrames.ThirdDerivative
variable {ι : Type} [Fintype ι] [DecidableEq ι]
variable {ρ : ℝ} {G : BondField ι → ℝ} {E E₃ W ψ ψ' : ℝ} {wa wq : ι → ℝ}
  {z w : ι → BondVector → BondVector} {u v : ι → ℝ}
theorem placeWeights_total_nonneg (hw : PlaceWeights wa wq W) : 0 ≤ W :=
  (Finset.sum_nonneg fun b _ => (hw.nonneg b).trans (hw.le b)).trans hw.sum
theorem abs_apply_fieldAlong_le (L : BondField ι →L[ℝ] ℝ) {c : ℝ} (hc : 0 ≤ c) (hw : PlaceWeights wa wq W)
    (hz : FieldC1Bound ρ z u) (hρ : 0 < ρ) (hA : IsAdmissible wa wq u ψ) (hψ : 0 ≤ ψ) (η : BondField ι)
    (hη : InOpenBalls ρ η) (hL : ∀ b (e : BondVector), |L (bondVariation b e)| ≤ c * wa b * ‖e‖) :
    |L (fieldAlong z η)| ≤ c * (ψ * W) := by
  conv_lhs => rw [eq_sum_bondVariation (fieldAlong z η), map_sum]
  refine (Finset.abs_sum_le_sum_abs _ _).trans ?_
  have s : ∑ b, |L (bondVariation b (fieldAlong z η b))| ≤ ∑ b, c * (wa b * u b) := by
    apply Finset.sum_le_sum
    intro b _
    have h1 := hL b (fieldAlong z η b)
    have n1 : ‖fieldAlong z η b‖ ≤ u b := hz.norm_le b _ (hη b)
    have := mul_le_mul_of_nonneg_left n1 (mul_nonneg hc (hw.nonneg b))
    calc _ ≤ _ := h1
      _ ≤ _ := this
      _ = _ := by ring
  refine s.trans ?_
  rw [← Finset.mul_sum]
  exact mul_le_mul_of_nonneg_left (sum_weight_mul_le hw hA hψ) hc
theorem bondGradNorm_secondDerivAlong_le (hJ : ThirdJetBound ρ G E E₃ wa) (hw : PlaceWeights wa wq W) (hE : 0 ≤ E) (hE₃ : 0 ≤ E₃)
    (hρ : 0 < ρ) (hz : FieldC1Bound ρ z u) (hv : FieldC1Bound ρ w v) (hA : IsAdmissible wa wq u ψ) (hB : IsAdmissible wa wq v ψ')
    (hψ : 0 ≤ ψ) (hψ' : 0 ≤ ψ') (b : ι) (η : BondField ι) (hη : InOpenBalls ρ η) :
    bondGradNorm (secondDerivAlong G z w) b η ≤ (E₃ * W ^ 2 + 2 * E * W) * (ψ * ψ') * wq b := by
  have hW := placeWeights_total_nonneg hw
  have wq0 : 0 ≤ wq b := (hw.nonneg b).trans (hw.le b)
  apply bondGradNorm_le (by positivity)
  intro e
  rw [secondDerivAlong_fderiv hJ.smooth hz.smooth hv.smooth, fieldAlongDeriv_bondVariation, fieldAlongDeriv_bondVariation]
  have n0 := norm_nonneg e
  have wb := hw.nonneg b
  have t1 : |fderiv ℝ (fderiv ℝ (fderiv ℝ G)) η (bondVariation b e) (fieldAlong z η) (fieldAlong w η)| ≤
      (E₃ * wa b * ‖e‖ * (ψ' * W)) * (ψ * W) := by
    have c1 : 0 ≤ E₃ * wa b * ‖e‖ * (ψ' * W) := by positivity
    refine abs_apply_fieldAlong_le ((ContinuousLinearMap.flip (fderiv ℝ (fderiv ℝ (fderiv ℝ G)) η (bondVariation b e)))
      (fieldAlong w η)) (c := E₃ * wa b * ‖e‖ * (ψ' * W)) c1 hw hz hρ hA hψ η hη ?_
    intro b' e'
    simp only [ContinuousLinearMap.flip_apply]
    have c2 : 0 ≤ E₃ * wa b * wa b' * ‖e‖ * ‖e'‖ := by
      have := hw.nonneg b'
      positivity
    have := abs_apply_fieldAlong_le (fderiv ℝ (fderiv ℝ (fderiv ℝ G)) η (bondVariation b e) (bondVariation b' e'))
      (c := E₃ * wa b * wa b' * ‖e‖ * ‖e'‖) c2 hw hv hρ hB hψ' η hη (fun b'' e'' => by
        have h3 := hJ.third η hη b b' b'' e e' e''
        calc _ ≤ _ := h3
          _ = _ := by ring)
    calc _ ≤ _ := this
      _ = _ := by ring
  have t2 : |fderiv ℝ (fderiv ℝ G) η (bondVariation b (fderiv ℝ (z b) (η b) e)) (fieldAlong w η)| ≤
      E * wa b * (u b * ‖e‖) * (ψ' * W) := by
    have c2 : 0 ≤ E * wa b * (u b * ‖e‖) := by
      have := fieldC1Bound_nonneg hz hρ b
      positivity
    refine abs_apply_fieldAlong_le _ c2 hw hv hρ hB hψ' η hη ?_
    intro b' e'
    have h2 := hJ.second η hη b b' (fderiv ℝ (z b) (η b) e) e'
    have n1 : ‖fderiv ℝ (z b) (η b) e‖ ≤ u b * ‖e‖ :=
      ((fderiv ℝ (z b) (η b)).le_opNorm e).trans
        (mul_le_mul_of_nonneg_right (hz.deriv_le b _ (hη b)) n0)
    have c3 : 0 ≤ E * wa b * wa b' := by
      have := hw.nonneg b'
      positivity
    have := mul_le_mul_of_nonneg_right n1 (norm_nonneg e')
    have := mul_le_mul_of_nonneg_left this c3
    calc _ ≤ _ := h2
      _ ≤ _ := this
      _ = _ := by ring
  have t3 : |fderiv ℝ (fderiv ℝ G) η (fieldAlong z η) (bondVariation b (fderiv ℝ (w b) (η b) e))| ≤
      E * wa b * (v b * ‖e‖) * (ψ * W) := by
    have c2 : 0 ≤ E * wa b * (v b * ‖e‖) := by
      have := fieldC1Bound_nonneg hv hρ b
      positivity
    refine abs_apply_fieldAlong_le ((ContinuousLinearMap.flip (fderiv ℝ (fderiv ℝ G) η))
      (bondVariation b (fderiv ℝ (w b) (η b) e))) c2 hw hz hρ hA hψ η hη ?_
    intro b' e'
    simp only [ContinuousLinearMap.flip_apply]
    have h2 := hJ.second η hη b' b e' (fderiv ℝ (w b) (η b) e)
    have n1 : ‖fderiv ℝ (w b) (η b) e‖ ≤ v b * ‖e‖ :=
      ((fderiv ℝ (w b) (η b)).le_opNorm e).trans
        (mul_le_mul_of_nonneg_right (hv.deriv_le b _ (hη b)) n0)
    have c3 : 0 ≤ E * wa b' * wa b := by
      have := hw.nonneg b'
      positivity
    have := mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left n1 (norm_nonneg e')) c3
    calc _ ≤ _ := h2
      _ ≤ _ := this
      _ = _ := by ring
  have a2 : wa b * u b ≤ ψ * wq b := hA b
  have a3 : wa b * v b ≤ ψ' * wq b := hB b
  have w1 := hw.le b
  have r1 : (E₃ * wa b * ‖e‖ * (ψ' * W)) * (ψ * W) ≤ E₃ * W ^ 2 * (ψ * ψ') * wq b * ‖e‖ := by
    have c : 0 ≤ E₃ * ‖e‖ * (ψ' * W) * (ψ * W) := by positivity
    have := mul_le_mul_of_nonneg_left w1 c
    calc _ = E₃ * ‖e‖ * (ψ' * W) * (ψ * W) * wa b := by ring
      _ ≤ _ := this
      _ = _ := by ring
  have r2 : E * wa b * (u b * ‖e‖) * (ψ' * W) ≤ E * W * (ψ * ψ') * wq b * ‖e‖ := by
    have c : 0 ≤ E * ‖e‖ * (ψ' * W) := by positivity
    have := mul_le_mul_of_nonneg_left a2 c
    calc _ = E * ‖e‖ * (ψ' * W) * (wa b * u b) := by ring
      _ ≤ _ := this
      _ = _ := by ring
  have r3 : E * wa b * (v b * ‖e‖) * (ψ * W) ≤ E * W * (ψ * ψ') * wq b * ‖e‖ := by
    have c : 0 ≤ E * ‖e‖ * (ψ * W) := by positivity
    have := mul_le_mul_of_nonneg_left a3 c
    calc _ = E * ‖e‖ * (ψ * W) * (wa b * v b) := by ring
      _ ≤ _ := this
      _ = _ := by ring
  have s1 := abs_add_le (fderiv ℝ (fderiv ℝ (fderiv ℝ G)) η (bondVariation b e) (fieldAlong z η) (fieldAlong w η) +
      fderiv ℝ (fderiv ℝ G) η (bondVariation b (fderiv ℝ (z b) (η b) e)) (fieldAlong w η))
    (fderiv ℝ (fderiv ℝ G) η (fieldAlong z η) (bondVariation b (fderiv ℝ (w b) (η b) e)))
  have s2 := abs_add_le (fderiv ℝ (fderiv ℝ (fderiv ℝ G)) η (bondVariation b e) (fieldAlong z η) (fieldAlong w η))
    (fderiv ℝ (fderiv ℝ G) η (bondVariation b (fderiv ℝ (z b) (η b) e)) (fieldAlong w η))
  have e9 : (E₃ * W ^ 2 + 2 * E * W) * (ψ * ψ') * wq b * ‖e‖ = E₃ * W ^ 2 * (ψ * ψ') * wq b * ‖e‖ +
      E * W * (ψ * ψ') * wq b * ‖e‖ + E * W * (ψ * ψ') * wq b * ‖e‖ := by ring
  rw [e9]
  linarith
theorem bondGradNorm_derivAlong_le (hJ : ThirdJetBound ρ G E E₃ wa) (hw : PlaceWeights wa wq W) (hE : 0 ≤ E) (hρ : 0 < ρ)
    (hz : FieldC1Bound ρ z u) (hA : IsAdmissible wa wq u ψ) (hψ : 0 ≤ ψ) (b : ι) (η : BondField ι)
    (hη : InOpenBalls ρ η) : bondGradNorm (derivAlong G z) b η ≤ (E * W + E) * ψ * wq b := by
  have hW := placeWeights_total_nonneg hw
  have wq0 : 0 ≤ wq b := (hw.nonneg b).trans (hw.le b)
  apply bondGradNorm_le (by positivity)
  intro e
  rw [derivAlong_fderiv hJ.smooth hz.smooth, fieldAlongDeriv_bondVariation]
  have n0 := norm_nonneg e
  have wb := hw.nonneg b
  have t1 : |fderiv ℝ (fderiv ℝ G) η (bondVariation b e) (fieldAlong z η)| ≤ E * wa b * ‖e‖ * (ψ * W) := by
    refine abs_apply_fieldAlong_le _ (by positivity) hw hz hρ hA hψ η hη ?_
    intro b' e'
    have h2 := hJ.second η hη b b' e e'
    calc _ ≤ _ := h2
      _ = _ := by ring
  have t2 : |fderiv ℝ G η (bondVariation b (fderiv ℝ (z b) (η b) e))| ≤ E * wa b * (u b * ‖e‖) := by
    have h1 := hJ.first η hη b (fderiv ℝ (z b) (η b) e)
    have n1 : ‖fderiv ℝ (z b) (η b) e‖ ≤ u b * ‖e‖ :=
      ((fderiv ℝ (z b) (η b)).le_opNorm e).trans
        (mul_le_mul_of_nonneg_right (hz.deriv_le b _ (hη b)) n0)
    exact h1.trans (mul_le_mul_of_nonneg_left n1 (by positivity))
  have w1 := hw.le b
  have r1 : E * wa b * ‖e‖ * (ψ * W) ≤ E * W * ψ * wq b * ‖e‖ := by
    have c : 0 ≤ E * ‖e‖ * (ψ * W) := by positivity
    have := mul_le_mul_of_nonneg_left w1 c
    calc _ = E * ‖e‖ * (ψ * W) * wa b := by ring
      _ ≤ _ := this
      _ = _ := by ring
  have r2 : E * wa b * (u b * ‖e‖) ≤ E * ψ * wq b * ‖e‖ := by
    have c : 0 ≤ E * ‖e‖ := by positivity
    have := mul_le_mul_of_nonneg_left (hA b) c
    calc _ = E * ‖e‖ * (wa b * u b) := by ring
      _ ≤ _ := this
      _ = _ := by ring
  have s1 := abs_add_le (fderiv ℝ (fderiv ℝ G) η (bondVariation b e) (fieldAlong z η))
    (fderiv ℝ G η (bondVariation b (fderiv ℝ (z b) (η b) e)))
  have e9 : (E * W + E) * ψ * wq b * ‖e‖ = E * W * ψ * wq b * ‖e‖ + E * ψ * wq b * ‖e‖ := by ring
  rw [e9]
  linarith
theorem FieldC2Bound.toFieldC1Bound (h : FieldC2Bound ρ z u) : FieldC1Bound ρ z u :=
  ⟨fun b => (h.smooth b).of_le (by norm_num), h.norm_le, h.deriv_le⟩
def fieldDerivAlong (z₁ z₂ : ι → BondVector → BondVector) (b : ι) (v : BondVector) : BondVector :=
  fderiv ℝ (z₂ b) v (z₁ b v)
theorem fieldAlongDeriv_fieldAlong (z₁ z₂ : ι → BondVector → BondVector) (η : BondField ι) :
    fieldAlongDeriv z₂ η (fieldAlong z₁ η) = fieldAlong (fieldDerivAlong z₁ z₂) η := by
  funext b
  simp [fieldAlongDeriv, fieldDerivAlong, fieldAlong]
theorem fieldDerivAlong_fieldC1Bound {z₁ z₂ : ι → BondVector → BondVector} {u₁ u₂ : ι → ℝ} (h₁ : FieldC2Bound ρ z₁ u₁)
    (h₂ : FieldC2Bound ρ z₂ u₂) (hρ : 0 < ρ) :
    FieldC1Bound ρ (fieldDerivAlong z₁ z₂) (fun b => 2 * (u₁ b * u₂ b)) := by
  have hs : ∀ b, ContDiff ℝ 1 (fieldDerivAlong z₁ z₂ b) := fun b =>
    ((h₂.smooth b).fderiv_right (m := 1) (by norm_num)).clm_apply
      ((h₁.smooth b).of_le (by norm_num))
  refine ⟨hs, fun b v hv => ?_, fun b v hv => ?_⟩
  · have a1 := h₁.norm_le b v hv
    have a2 := h₂.deriv_le b v hv
    have u1 := (norm_nonneg _).trans a1
    have u2 := (norm_nonneg _).trans a2
    have := ((fderiv ℝ (z₂ b) v).le_opNorm (z₁ b v)).trans (mul_le_mul a2 a1 (norm_nonneg _) u2)
    simp only [fieldDerivAlong]
    nlinarith [mul_nonneg u1 u2]
  · have hd2 : HasFDerivAt (fderiv ℝ (z₂ b)) (fderiv ℝ (fderiv ℝ (z₂ b)) v) v :=
      (((h₂.smooth b).fderiv_right (m := 1) (by norm_num)).differentiable (by norm_num) v).hasFDerivAt
    have hd1 : HasFDerivAt (z₁ b) (fderiv ℝ (z₁ b) v) v :=
      (((h₁.smooth b).differentiable (by norm_num)) v).hasFDerivAt
    have h3 : fderiv ℝ (fieldDerivAlong z₁ z₂ b) v = _ := (hd2.clm_apply hd1).fderiv
    rw [h3]
    have a1 := h₁.norm_le b v hv
    have a2 := h₂.deriv_le b v hv
    have a3 := h₁.deriv_le b v hv
    have a4 := h₂.second_deriv_le b v hv
    have u1 := (norm_nonneg _).trans a1
    have u2 := (norm_nonneg _).trans a2
    refine (_root_.norm_add_le _ _).trans ?_
    have c1 : ‖(fderiv ℝ (z₂ b) v).comp (fderiv ℝ (z₁ b) v)‖ ≤ u₂ b * u₁ b :=
      (ContinuousLinearMap.opNorm_comp_le _ _).trans (mul_le_mul a2 a3 (norm_nonneg _) u2)
    have c2 : ‖(fderiv ℝ (fderiv ℝ (z₂ b)) v).flip (z₁ b v)‖ ≤ u₂ b * u₁ b := by
      refine ((ContinuousLinearMap.flip (fderiv ℝ (fderiv ℝ (z₂ b)) v)).le_opNorm _).trans ?_
      rw [ContinuousLinearMap.opNorm_flip]
      exact mul_le_mul a4 a1 (norm_nonneg _) u2
    linarith [mul_comm (u₁ b) (u₂ b)]
def thirdDerivRemainder (G : BondField ι → ℝ) (z₁ z₂ z₃ z₁₂ z₁₃ z₂₃ z₁₂₃ : ι → BondVector → BondVector)
    (η : BondField ι) : ℝ :=
  secondDerivAlong G z₁₂ z₃ η - secondDerivAlong G (fieldDerivAlong z₁ z₂) z₃ η - secondDerivAlong G z₂ (fieldDerivAlong z₁ z₃) η + secondDerivAlong G z₁₃ z₂ η +
    secondDerivAlong G z₂₃ z₁ η + derivAlong G z₁₂₃ η
theorem thirdDerivAlong_split (h : ContDiff ℝ 3 G) {z₁ z₂ z₃ z₁₂ z₁₃ z₂₃ z₁₂₃ : ι → BondVector → BondVector}
    (h₂ : ∀ b, ContDiff ℝ 1 (z₂ b)) (h₃ : ∀ b, ContDiff ℝ 1 (z₃ b)) (η : BondField ι) :
    thirdDerivAlong G z₁ z₂ z₃ z₁₂ z₁₃ z₂₃ z₁₂₃ η =
      fderiv ℝ (secondDerivAlong G z₂ z₃) η (fieldAlong z₁ η) + thirdDerivRemainder G z₁ z₂ z₃ z₁₂ z₁₃ z₂₃ z₁₂₃ η := by
  rw [secondDerivAlong_fderiv h h₂ h₃, fieldAlongDeriv_fieldAlong, fieldAlongDeriv_fieldAlong]
  simp only [thirdDerivAlong, thirdDerivRemainder, secondDerivAlong]
  ring
def coordUnit (i : Fin 3) : BondVector := EuclideanSpace.single i (1 : ℝ)
theorem norm_coordUnit (i : Fin 3) : ‖coordUnit i‖ = 1 := by simp [coordUnit]
theorem eq_sum_coordUnit (v : BondVector) : v = ∑ i, v i • coordUnit i := by
  ext l
  simp [coordUnit, Finset.sum_apply, Pi.single_apply]
theorem apply_eq_sum_coordUnit (L : BondField ι →L[ℝ] ℝ) (p : BondField ι) :
    L p = ∑ b, ∑ i, (p b) i * L (bondVariation b (coordUnit i)) := by
  conv_lhs => rw [eq_sum_bondVariation p, map_sum]
  apply Finset.sum_congr rfl
  intro b _
  have e : bondVariation b (p b) = ∑ i, (p b) i • bondVariation b (coordUnit i) := by
    conv_lhs => rw [eq_sum_coordUnit (p b)]
    funext l
    by_cases h : l = b
    · subst h
      simp [bondVariation, Finset.sum_apply]
    · simp [bondVariation, Finset.sum_apply, Pi.single_eq_of_ne h]
  rw [e, map_sum]
  simp
end YangMills.Construction.ColdStepAtMirrorFrames.ThirdDerivative
end
noncomputable section
open MeasureTheory Set Filter Topology
namespace YangMills.Construction.ColdStepAtMirrorFrames.ThirdDerivative
variable {ι : Type} [Fintype ι] [DecidableEq ι]
variable {ρ : ℝ} {p : ℝ → ℝ} {m κ : ℝ} {d : ι → ι → ℝ} {Ψ : BondField ι → ℝ} {K : ι → ι → ℝ}
  {c₁ W : ℝ}
theorem pseudoMetric_nonneg (h : IsPseudoMetricOnBonds d) (b b' : ι) : 0 ≤ d b b' := by apply _root_.YangMills.Construction.ConvexMeasures.LocalCovariance.pseudoMetric_nonneg <;> assumption
theorem convexMeasure_kernel_nonneg (h : ConvexMeasureHyp ρ p m κ d Ψ K c₁ W) (b b' : ι) : 0 ≤ K b b' := by
  have := h.convex.kernel 0 (inOpenBalls_zero h.pos) b b' (coordUnit 0) (coordUnit 0)
  rw [norm_coordUnit, mul_one, mul_one] at this
  exact (abs_nonneg _).trans this
theorem convexMeasure_kernel_sum_le (h : ConvexMeasureHyp ρ p m κ d Ψ K c₁ W) (b : ι) : ∑ b', K b b' ≤ c₁ * m := by
  refine le_trans (Finset.sum_le_sum fun b' _ => ?_) (h.standingConstraints b)
  have h1 : 1 ≤ Real.exp (κ * d b b') :=
    Real.one_le_exp (mul_nonneg h.rate_pos.le (pseudoMetric_nonneg h.dist b b'))
  have := convexMeasure_kernel_nonneg h b b'
  nlinarith
theorem inOpenBalls_smul {η : BondField ι} (hη : InOpenBalls ρ η) {t : ℝ} (h0 : 0 ≤ t) (h1 : t ≤ 1) :
    InOpenBalls ρ (t • η) := by
  intro b
  have : ‖(t • η) b‖ = t * ‖η b‖ := by
    simp [norm_smul, abs_of_nonneg h0]
  rw [this]
  have := norm_nonneg (η b)
  have := hη b
  nlinarith
theorem abs_bondPartialDeriv_sub_le (h : ConvexMeasureHyp ρ p m κ d Ψ K c₁ W) (b : ι) (e : BondVector)
    (η : BondField ι) (hη : InOpenBalls ρ η) :
    |bondPartialDeriv Ψ b η e - bondPartialDeriv Ψ b 0 e| ≤ (∑ b', K b b' * ‖η b'‖) * ‖e‖ := by
  have hP : ContDiff ℝ 1 (fun ζ => bondPartialDeriv Ψ b ζ e) :=
    bondPartialDeriv_contDiff (n := 1) (h.data.smooth.of_le (by norm_num)) b e
  have hdP : Differentiable ℝ (fun ζ => bondPartialDeriv Ψ b ζ e) := hP.differentiable (by norm_num)
  set f : ℝ → ℝ := fun t => bondPartialDeriv Ψ b (t • η) e with hf
  have hder : ∀ t, HasDerivAt f (fderiv ℝ (fun ζ => bondPartialDeriv Ψ b ζ e) (t • η) η) t := by
    intro t
    have h1 : HasDerivAt (fun s : ℝ => s • η) η t := by
      simpa using (hasDerivAt_id t).smul_const η
    exact ((hdP (t • η)).hasFDerivAt).comp_hasDerivAt t h1
  obtain ⟨c, hc, hs⟩ := exists_hasDerivAt_eq_slope f _ (by norm_num : (0 : ℝ) < 1)
    (fun x _ => (hder x).continuousAt.continuousWithinAt) (fun x _ => hder x)
  have e1 : f 1 - f 0 = fderiv ℝ (fun ζ => bondPartialDeriv Ψ b ζ e) (c • η) η := by
    have := hs
    simp only [sub_zero, div_one] at this
    exact this.symm
  have e2 : f 1 = bondPartialDeriv Ψ b η e := by simp [hf]
  have e3 : f 0 = bondPartialDeriv Ψ b 0 e := by simp [hf]
  rw [← e2, ← e3, e1]
  have hζ := inOpenBalls_smul hη hc.1.le hc.2.le
  have hL : ∀ L : BondField ι →L[ℝ] ℝ, L η = ∑ b', L (bondVariation b' (η b')) := fun L => by
    conv_lhs => rw [eq_sum_bondVariation η, map_sum]
  rw [hL]
  refine (Finset.abs_sum_le_sum_abs _ _).trans ?_
  rw [Finset.sum_mul]
  apply Finset.sum_le_sum
  intro b' _
  have := h.convex.kernel (c • η) hζ b b' e (η b')
  exact le_trans this (le_of_eq (by ring))
theorem kernel_sum_norm_le (h : ConvexMeasureHyp ρ p m κ d Ψ K c₁ W) (b : ι) (η : BondField ι)
    (hη : InOpenBalls ρ η) : ∑ b', K b b' * ‖η b'‖ ≤ ρ * (c₁ * m) := by
  have h1 : ∑ b', K b b' * ‖η b'‖ ≤ ∑ b', K b b' * ρ := Finset.sum_le_sum fun b' _ =>
    mul_le_mul_of_nonneg_left (hη b').le (convexMeasure_kernel_nonneg h b b')
  rw [← Finset.sum_mul] at h1
  have := mul_le_mul_of_nonneg_right (convexMeasure_kernel_sum_le h b) h.pos.le
  linarith
theorem abs_bondPartialDeriv_le (h : ConvexMeasureHyp ρ p m κ d Ψ K c₁ W) (b : ι) (e : BondVector)
    (η : BondField ι) (hη : InOpenBalls ρ η) :
    |bondPartialDeriv Ψ b η e| ≤ (1 + ρ * c₁) * m * ‖e‖ := by
  have h1 := abs_bondPartialDeriv_sub_le h b e η hη
  have h2 := h.slope_zero b e
  have h3 := kernel_sum_norm_le h b η hη
  have n0 := norm_nonneg e
  have h4 : Real.sqrt m ≤ m := by
    have := h.one_le
    rw [Real.sqrt_le_left (by linarith)]
    nlinarith
  have s1 : |bondPartialDeriv Ψ b η e| ≤ |bondPartialDeriv Ψ b η e - bondPartialDeriv Ψ b 0 e| + |bondPartialDeriv Ψ b 0 e| := by
    have := abs_add_le (bondPartialDeriv Ψ b η e - bondPartialDeriv Ψ b 0 e) (bondPartialDeriv Ψ b 0 e)
    simpa using this
  have s2 := mul_le_mul_of_nonneg_right h3 n0
  have s3 := mul_le_mul_of_nonneg_right h4 n0
  calc _ ≤ _ := s1
    _ ≤ ρ * (c₁ * m) * ‖e‖ + m * ‖e‖ := by linarith
    _ = _ := by ring
theorem ballL2Norm_sum_le {s : Finset ι} {f : ι → BondField ι → ℝ}
    (hd : IsCutoffMeasureData ρ (extendedCutoff ρ p) Ψ) (hf : ∀ i, Continuous (f i)) :
    ballL2Norm (extendedCutoff ρ p) Ψ (fun η => ∑ i ∈ s, f i η) ≤
      ∑ i ∈ s, ballL2Norm (extendedCutoff ρ p) Ψ (f i) := by
  classical
  induction s using Finset.induction_on with
  | empty =>
    simp only [Finset.sum_empty]
    rw [ballL2Norm_const hd le_rfl]
  | insert a s ha ih =>
    simp only [Finset.sum_insert ha]
    have c2 : Continuous fun η => ∑ i ∈ s, f i η := continuous_finsetSum _ fun i _ => hf i
    refine (ballL2Norm_add_le hd (hf a) c2).trans ?_
    linarith
variable (hMom : GaussianMomentBound) (hR : CutoffFactorIsRadialCutoff)
include hMom hR in
theorem ballExpectation_norm_pow_le (h : ConvexMeasureHyp ρ p m κ d Ψ K c₁ W) (q : ℕ) (b₀ : ι) :
    ballExpectation (extendedCutoff ρ p) Ψ (fun η => ‖η b₀‖ ^ (2 * q)) ≤
      (∏ k ∈ Finset.range q, (4 * (k : ℝ) + 8 * W)) / m ^ q :=
  hMom ι ρ m κ W d Ψ K (extendedCutoff ρ p) h.pos (by linarith [h.one_le]) h.rate_pos.le
    (extendedCutoff_isRadialCutoff hR h.pos h.cutoff) h.dist h.convex h.weight_sum h.slope_zero q b₀
theorem convexMeasure_weight_nonneg (h : ConvexMeasureHyp ρ p m κ d Ψ K c₁ W) (b₀ : ι) : 0 ≤ W :=
  (Finset.sum_nonneg fun b _ => (Real.exp_pos _).le).trans (h.weight_sum b₀)
include hMom hR in
theorem ballL2Norm_bondPartialDeriv_le (h : ConvexMeasureHyp ρ p m κ d Ψ K c₁ W) (b : ι) (e : BondVector) (he : ‖e‖ = 1) :
    ballL2Norm (extendedCutoff ρ p) Ψ (fun η => bondPartialDeriv Ψ b η e) ≤
      (1 + c₁ * Real.sqrt (8 * W)) * Real.sqrt m := by
  have hd := h.data
  have hm : 0 < m := by linarith [h.one_le]
  have hsm : 0 < Real.sqrt m := Real.sqrt_pos.mpr hm
  have cP : Continuous (fun η => bondPartialDeriv Ψ b η e) :=
    (bondPartialDeriv_contDiff (n := 1) (hd.smooth.of_le (by norm_num)) b e).continuous
  have cn : ∀ b', Continuous fun η : BondField ι => K b b' * ‖η b'‖ := fun b' =>
    continuous_const.mul (continuous_apply b').norm
  have c2 : Continuous fun η : BondField ι => Real.sqrt m + ∑ b', K b b' * ‖η b'‖ :=
    continuous_const.add (continuous_finsetSum _ fun b' _ => cn b')
  have hle : ∀ η, InOpenBalls ρ η → |bondPartialDeriv Ψ b η e| ≤ |Real.sqrt m + ∑ b', K b b' * ‖η b'‖| := by
    intro η hη
    have h1 := abs_bondPartialDeriv_sub_le h b e η hη
    have h2 := h.slope_zero b e
    rw [he, mul_one] at h1 h2
    have s1 : |bondPartialDeriv Ψ b η e| ≤ |bondPartialDeriv Ψ b η e - bondPartialDeriv Ψ b 0 e| + |bondPartialDeriv Ψ b 0 e| := by
      have := abs_add_le (bondPartialDeriv Ψ b η e - bondPartialDeriv Ψ b 0 e) (bondPartialDeriv Ψ b 0 e)
      simpa using this
    have hs : 0 ≤ ∑ b', K b b' * ‖η b'‖ := Finset.sum_nonneg fun b' _ =>
      mul_nonneg (convexMeasure_kernel_nonneg h b b') (norm_nonneg _)
    have hz : 0 ≤ Real.sqrt m + ∑ b', K b b' * ‖η b'‖ := by linarith
    rw [abs_of_nonneg hz]
    linarith
  refine (ballL2Norm_le_of_abs_le hd cP c2 hle).trans ?_
  refine (ballL2Norm_add_le hd continuous_const (continuous_finsetSum _ fun b' _ => cn b')).trans ?_
  rw [ballL2Norm_const hd hsm.le]
  have hW : 0 ≤ W := convexMeasure_weight_nonneg h b
  have hnorm : ∀ b', ballL2Norm (extendedCutoff ρ p) Ψ (fun η : BondField ι => K b b' * ‖η b'‖) ≤
      K b b' * (Real.sqrt (8 * W) / Real.sqrt m) := by
    intro b'
    rw [ballL2Norm_const_mul hd, abs_of_nonneg (convexMeasure_kernel_nonneg h b b')]
    apply mul_le_mul_of_nonneg_left _ (convexMeasure_kernel_nonneg h b b')
    unfold ballL2Norm
    rw [← Real.sqrt_div (by positivity)]
    apply Real.sqrt_le_sqrt
    have := ballExpectation_norm_pow_le hMom hR h 1 b'
    simp only [mul_one, Finset.prod_range_one, Nat.cast_zero, mul_zero, zero_add, pow_one] at this
    exact this
  have s1 := (ballL2Norm_sum_le (s := Finset.univ) hd cn).trans (Finset.sum_le_sum fun b' _ => hnorm b')
  rw [← Finset.sum_mul] at s1
  have s2 : (∑ b', K b b') * (Real.sqrt (8 * W) / Real.sqrt m) ≤
      (c₁ * m) * (Real.sqrt (8 * W) / Real.sqrt m) :=
    mul_le_mul_of_nonneg_right (convexMeasure_kernel_sum_le h b) (by positivity)
  have e1 : (c₁ * m) * (Real.sqrt (8 * W) / Real.sqrt m) = c₁ * Real.sqrt (8 * W) * Real.sqrt m := by
    have e0 : (c₁ * m) * (Real.sqrt (8 * W) / Real.sqrt m) =
        c₁ * Real.sqrt (8 * W) * (m / Real.sqrt m) := by ring
    rw [e0, Real.div_sqrt]
  have e2 : (1 + c₁ * Real.sqrt (8 * W)) * Real.sqrt m =
      Real.sqrt m + c₁ * Real.sqrt (8 * W) * Real.sqrt m := by ring
  rw [e2]
  linarith
end YangMills.Construction.ColdStepAtMirrorFrames.ThirdDerivative
end
noncomputable section
open MeasureTheory Set Filter Topology
namespace YangMills.Construction.ColdStepAtMirrorFrames.ThirdDerivative
variable {ρ : ℝ} {p : ℝ → ℝ}
theorem exists_rimBoundConst (hρ : 0 < ρ) (hp : IsCutoff ρ p) : ∃ c, RimBoundConst ρ p c := by
  obtain ⟨c, h1, h2⟩ := rim_terms_le hρ hp
  exact ⟨c, h1, h2⟩
theorem slopePower_sq_le {ε : ℝ} (hρ : 0 < ρ) (hp : IsCutoff ρ p) (j : ℕ) {u : ℝ} (hu : u < ρ) :
    slopePower ρ p ε j u ^ 2 ≤ slopePower ρ p ε (2 * j) u := by
  simp only [slopePower]
  have a0 := outerStep_nonneg (ρ := ρ) u
  have a1 := outerStep_le_one (ρ := ρ) u
  have b0 := levelStep_nonneg (ρ := ρ) (p := p) (ε := ε) u
  have b1 := levelStep_le_one (ρ := ρ) (p := p) (ε := ε) u
  have c0 : 0 ≤ cutoffSlope ρ p u ^ (2 * j) := pow_nonneg (cutoffSlope_nonneg hρ hp hu) _
  have e : (outerStep ρ u * cutoffSlope ρ p u ^ j * levelStep ρ p ε u) ^ 2 =
      (outerStep ρ u * outerStep ρ u) * cutoffSlope ρ p u ^ (2 * j) * (levelStep ρ p ε u * levelStep ρ p ε u) := by
    rw [two_mul, pow_add]
    ring
  rw [e]
  have h1 : outerStep ρ u * outerStep ρ u ≤ outerStep ρ u := mul_le_of_le_one_left a0 a1
  have h2 : levelStep ρ p ε u * levelStep ρ p ε u ≤ levelStep ρ p ε u := mul_le_of_le_one_left b0 b1
  exact mul_le_mul (mul_le_mul_of_nonneg_right h1 c0) h2 (by positivity) (by positivity)
theorem rim_moment_arith {c c0 c2 c4 A m L P M0 M2 M4 mb : ℝ} (hc0 : 0 ≤ c0) (hc2 : 0 ≤ c2) (hc4 : 0 ≤ c4)
    (hA : 1 ≤ A) (hm : 1 ≤ m) (hL : 0 ≤ L) (hP : 0 ≤ P) (hmb0 : 0 ≤ mb) (hmb : mb ≤ L * (P / m ^ 5))
    (h0 : M0 ≤ c0 * (A * m) ^ 0 * mb) (h2 : M2 ≤ c2 * (A * m) ^ 2 * mb)
    (h4 : M4 ≤ c4 * (A * m) ^ 4 * mb) :
    3 * c ^ 2 * (M0 + (M2 + M4)) ≤ 3 * c ^ 2 * (c0 + c2 + c4) * A ^ 4 * (L * P) / m := by
  have hB1 : 1 ≤ A * m := by nlinarith
  set B := A * m with hB
  have b2 : B ^ 2 ≤ B ^ 4 := pow_le_pow_right₀ hB1 (by norm_num)
  have b0 : (1 : ℝ) ≤ B ^ 4 := one_le_pow₀ hB1
  have t0 : c0 * B ^ 0 * mb ≤ c0 * B ^ 4 * mb := by
    rw [pow_zero, mul_one]
    apply mul_le_mul_of_nonneg_right _ hmb0
    nlinarith
  have t2 : c2 * B ^ 2 * mb ≤ c2 * B ^ 4 * mb :=
    mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left b2 hc2) hmb0
  have s0 : M0 + (M2 + M4) ≤ (c0 + c2 + c4) * B ^ 4 * mb := by
    have e : (c0 + c2 + c4) * B ^ 4 * mb = c0 * B ^ 4 * mb + c2 * B ^ 4 * mb + c4 * B ^ 4 * mb := by
      ring
    rw [e]
    linarith
  have s1 : (c0 + c2 + c4) * B ^ 4 * mb ≤ (c0 + c2 + c4) * B ^ 4 * (L * (P / m ^ 5)) :=
    mul_le_mul_of_nonneg_left hmb (by positivity)
  have e2 : (c0 + c2 + c4) * B ^ 4 * (L * (P / m ^ 5)) = (c0 + c2 + c4) * A ^ 4 * (L * P) / m := by
    simp only [hB]
    field_simp
  have s3 := mul_le_mul_of_nonneg_left (s0.trans (s1.trans (le_of_eq e2))) (by positivity : (0 : ℝ) ≤ 3 * c ^ 2)
  refine s3.trans (le_of_eq ?_)
  ring
theorem ballL2Norm_rimBound_le (hMom : GaussianMomentBound) (hR : CutoffFactorIsRadialCutoff) (hρ : 0 < ρ)
    (hp : IsCutoff ρ p) {c : ℝ} (hc : RimBoundConst ρ p c) (c₁ W : ℝ) (hc₁ : 0 ≤ c₁) (hW : 0 ≤ W) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ (ι : Type) [Fintype ι] [DecidableEq ι] (m κ : ℝ) (d : ι → ι → ℝ)
      (Ψ : BondField ι → ℝ) (K : ι → ι → ℝ), ConvexMeasureHyp ρ p m κ d Ψ K c₁ W →
      ∀ (b : ι) (ε : ℝ), 0 < ε →
        ballL2Norm (extendedCutoff ρ p) Ψ (fun η => rimBound ρ p c ε ‖η b‖) ≤ C / Real.sqrt m := by
  obtain ⟨c0, hc0, m0⟩ := slopeMoment_le hR hρ hp 0
  obtain ⟨c2, hc2, m2⟩ := slopeMoment_le hR hρ hp 2
  obtain ⟨c4, hc4, m4⟩ := slopeMoment_le hR hρ hp 4
  set A := 1 + ρ * c₁ with hA
  have hA1 : 1 ≤ A := by
    have := mul_nonneg hρ.le hc₁
    simp only [hA]
    linarith
  set P : ℝ := ∏ k ∈ Finset.range 5, (4 * (k : ℝ) + 8 * W) with hP
  have hP0 : 0 ≤ P := Finset.prod_nonneg fun k _ => by positivity
  set Cq := 3 * c ^ 2 * (c0 + c2 + c4) * A ^ 4 * ((2 / ρ) ^ 10 * P) with hCq
  have hCq0 : 0 ≤ Cq := by positivity
  refine ⟨Real.sqrt Cq, Real.sqrt_nonneg _, ?_⟩
  intro ι _ _ m κ d Ψ K h b ε hε
  have hd := h.data
  have hm1 := h.one_le
  have hε2 : 0 < ε / 2 := by positivity
  set B := A * m with hB
  have hB1 : 1 ≤ B := by nlinarith
  set β : BondField ι → ℝ := fun η => (2 / ρ) ^ 10 * ‖η b‖ ^ (2 * 5) with hβ
  have hctx : SlopeMomentHyp ρ p Ψ b B β := by
    refine ⟨hρ, hp, hd, hB1, fun η hη => ?_, by fun_prop, fun η _ => by positivity, fun η _ hu => ?_⟩
    · exact abs_bondPartialDeriv_le h b (η b) η hη
    · simp only [hβ]
      have e : (2 / ρ) ^ 10 * ‖η b‖ ^ (2 * 5) = (2 * ‖η b‖ / ρ) ^ 10 := by
        rw [div_pow, div_pow, mul_pow]
        norm_num
        ring
      rw [e]
      apply one_le_pow₀
      rw [le_div_iff₀ hρ]
      linarith
  have hmβ : ballExpectation (extendedCutoff ρ p) Ψ β ≤ (2 / ρ) ^ 10 * (P / m ^ 5) := by
    simp only [hβ]
    rw [ballExpectation_const_mul]
    exact mul_le_mul_of_nonneg_left (ballExpectation_norm_pow_le hMom hR h 5 b) (by positivity)
  have hmβ0 : 0 ≤ ballExpectation (extendedCutoff ρ p) Ψ β := ballExpectation_nonneg hd hctx.weight_nonneg
  have M0 := m0 ι Ψ b B β (ε / 2) hctx hε2
  have M2 := m2 ι Ψ b B β (ε / 2) hctx hε2
  have M4 := m4 ι Ψ b B β (ε / 2) hctx hε2
  have hn : Continuous fun η : BondField ι => ‖η b‖ := (continuous_apply b).norm
  have cP : ∀ j, Continuous fun η : BondField ι => slopePower ρ p (ε / 2) j ‖η b‖ := fun j =>
    (slopePower_continuous hR hρ hp hε2 j).comp hn
  have cO : Continuous fun η : BondField ι => rimBound ρ p c ε ‖η b‖ :=
    (rimBound_continuous hR hρ hp hε c).comp hn
  have hsq : ballExpectation (extendedCutoff ρ p) Ψ (fun η => rimBound ρ p c ε ‖η b‖ ^ 2) ≤
      ballExpectation (extendedCutoff ρ p) Ψ (fun η => 3 * c ^ 2 * (slopePower ρ p (ε / 2) 0 ‖η b‖ +
        (slopePower ρ p (ε / 2) 2 ‖η b‖ + slopePower ρ p (ε / 2) 4 ‖η b‖))) := by
    apply ballExpectation_mono hd (cO.pow 2) (continuous_const.mul ((cP 0).add ((cP 2).add (cP 4))))
    intro η hη
    have hu := hη b
    show rimBound ρ p c ε ‖η b‖ ^ 2 ≤ 3 * c ^ 2 * (slopePower ρ p (ε / 2) 0 ‖η b‖ +
        (slopePower ρ p (ε / 2) 2 ‖η b‖ + slopePower ρ p (ε / 2) 4 ‖η b‖))
    simp only [rimBound]
    have q0 := slopePower_sq_le (ε := ε / 2) hρ hp 0 hu
    have q1 := slopePower_sq_le (ε := ε / 2) hρ hp 1 hu
    have q2 := slopePower_sq_le (ε := ε / 2) hρ hp 2 hu
    simp only [Nat.mul_zero, Nat.mul_one, Nat.reduceMul] at q0 q1 q2
    set x := slopePower ρ p (ε / 2) 0 ‖η b‖
    set y := slopePower ρ p (ε / 2) 1 ‖η b‖
    set z := slopePower ρ p (ε / 2) 2 ‖η b‖
    have e1 : (x + y + z) ^ 2 ≤ 3 * (x ^ 2 + y ^ 2 + z ^ 2) := by
      nlinarith [sq_nonneg (x - y), sq_nonneg (y - z), sq_nonneg (x - z)]
    have e2 : (c * (x + y + z)) ^ 2 = c ^ 2 * (x + y + z) ^ 2 := by ring
    rw [e2]
    have c2n : 0 ≤ c ^ 2 := sq_nonneg c
    have := mul_le_mul_of_nonneg_left e1 c2n
    have h3 : 3 * (x ^ 2 + y ^ 2 + z ^ 2) ≤ 3 * (x + (z + slopePower ρ p (ε / 2) 4 ‖η b‖)) := by linarith
    have := mul_le_mul_of_nonneg_left h3 c2n
    nlinarith
  have c24 : Continuous fun η : BondField ι =>
      slopePower ρ p (ε / 2) 2 ‖η b‖ + slopePower ρ p (ε / 2) 4 ‖η b‖ := (cP 2).add (cP 4)
  rw [ballExpectation_const_mul, ballExpectation_add hd (cP 0) c24, ballExpectation_add hd (cP 2) (cP 4)] at hsq
  have hfin : ballExpectation (extendedCutoff ρ p) Ψ (fun η => rimBound ρ p c ε ‖η b‖ ^ 2) ≤ Cq / m :=
    hsq.trans (rim_moment_arith hc0 hc2 hc4 hA1 hm1 (by positivity) hP0 hmβ0 hmβ M0 M2 M4)
  unfold ballL2Norm
  rw [← Real.sqrt_div hCq0]
  exact Real.sqrt_le_sqrt hfin
end YangMills.Construction.ColdStepAtMirrorFrames.ThirdDerivative
end
noncomputable section
namespace YangMills.Construction.ColdStepAtMirrorFrames.ThirdDerivative
variable {X : Type}
variable {δ : X → X → ℝ}
theorem expWeight_nonneg (r : ℝ) (x y : X) : 0 ≤ expWeight δ r x y := (Real.exp_pos _).le
theorem expWeight_le_one (h : IsSiteDistance δ) {r : ℝ} (hr : 0 ≤ r) (x y : X) : expWeight δ r x y ≤ 1 := by
  apply Real.exp_le_one_iff.mpr
  have := mul_nonneg hr (h.nonneg x y)
  linarith
theorem expWeight_anti (h : IsSiteDistance δ) {r s : ℝ} (hrs : r ≤ s) (x y : X) :
    expWeight δ s x y ≤ expWeight δ r x y := by
  apply Real.exp_le_exp.mpr
  have := mul_le_mul_of_nonneg_right hrs (h.nonneg x y)
  linarith
theorem expWeight_symm (h : IsSiteDistance δ) (r : ℝ) (x y : X) : expWeight δ r x y = expWeight δ r y x := by
  simp only [expWeight, h.symm x y]
variable {ι : Type} [Fintype ι] {loc : ι → X}
theorem sum_expWeight_le_of_le (h : IsSiteDistance δ) {θ r W : ℝ} (hθ : θ ≤ r)
    (hW : ∀ z, ∑ b, expWeight δ θ (loc b) z ≤ W) (z : X) : ∑ b, expWeight δ r (loc b) z ≤ W :=
  (Finset.sum_le_sum fun b _ => expWeight_anti h hθ _ _).trans (hW z)
theorem sum_expWeight_mul_le (h : IsSiteDistance δ) {θ r₁ r₂ W : ℝ} (hθ : 0 ≤ θ) (h1 : 2 * θ ≤ r₁)
    (h2 : θ ≤ r₂) (hW : ∀ z, ∑ b, expWeight δ θ (loc b) z ≤ W) (x y : X) :
    ∑ b, expWeight δ r₁ x (loc b) * expWeight δ r₂ (loc b) y ≤ W * expWeight δ θ x y := by
  have key : ∀ b, expWeight δ r₁ x (loc b) * expWeight δ r₂ (loc b) y ≤ expWeight δ θ (loc b) x * expWeight δ θ x y := by
    intro b
    simp only [expWeight]
    rw [← Real.exp_add, ← Real.exp_add]
    apply Real.exp_le_exp.mpr
    have n1 := h.nonneg x (loc b)
    have n2 := h.nonneg (loc b) y
    have t := h.triangle x (loc b) y
    have s := h.symm (loc b) x
    have a1 := mul_le_mul_of_nonneg_right h1 n1
    have a2 := mul_le_mul_of_nonneg_right h2 n2
    have a3 := mul_le_mul_of_nonneg_left t hθ
    rw [s]
    nlinarith
  refine (Finset.sum_le_sum fun b _ => key b).trans ?_
  rw [← Finset.sum_mul]
  exact mul_le_mul_of_nonneg_right (hW x) (expWeight_nonneg _ _ _)
theorem sum_sum_expWeight_le (h : IsSiteDistance δ) {κ θ₀ r₁ r₂ W : ℝ} (hκ : 0 ≤ κ) (h0 : θ₀ ≤ κ / 4)
    (h1 : κ ≤ r₁) (h2 : κ / 4 ≤ r₂) (hW : ∀ z, ∑ b, expWeight δ θ₀ (loc b) z ≤ W) (x y : X) :
    ∑ b₁, ∑ b₂, expWeight δ r₁ x (loc b₁) * expWeight δ κ (loc b₁) (loc b₂) * expWeight δ r₂ (loc b₂) y ≤
      W * (W * expWeight δ (κ / 4) x y) := by
  have hW2 : ∀ z, ∑ b, expWeight δ (κ / 2) (loc b) z ≤ W := sum_expWeight_le_of_le h (by linarith) hW
  have hW4 : ∀ z, ∑ b, expWeight δ (κ / 4) (loc b) z ≤ W := sum_expWeight_le_of_le h h0 hW
  rw [Finset.sum_comm]
  have in1 : ∀ b₂, ∑ b₁, expWeight δ r₁ x (loc b₁) * expWeight δ κ (loc b₁) (loc b₂) * expWeight δ r₂ (loc b₂) y ≤
      W * expWeight δ (κ / 2) x (loc b₂) * expWeight δ r₂ (loc b₂) y := by
    intro b₂
    rw [← Finset.sum_mul]
    apply mul_le_mul_of_nonneg_right _ (expWeight_nonneg _ _ _)
    exact sum_expWeight_mul_le h (by positivity) (by linarith) (by linarith) hW2 x (loc b₂)
  refine (Finset.sum_le_sum fun b₂ _ => in1 b₂).trans ?_
  have e : ∑ b₂, W * expWeight δ (κ / 2) x (loc b₂) * expWeight δ r₂ (loc b₂) y =
      W * ∑ b₂, expWeight δ (κ / 2) x (loc b₂) * expWeight δ r₂ (loc b₂) y := by
    rw [Finset.mul_sum]
    exact Finset.sum_congr rfl fun b₂ _ => by ring
  rw [e]
  have hW0 : 0 ≤ W := (Finset.sum_nonneg fun b _ => expWeight_nonneg _ _ _) |>.trans (hW4 x) |> fun t => t
  exact mul_le_mul_of_nonneg_left (sum_expWeight_mul_le h (by positivity) (by linarith) h2 hW4 x y) hW0
end YangMills.Construction.ColdStepAtMirrorFrames.ThirdDerivative
end
noncomputable section
open MeasureTheory Set Filter Topology
namespace YangMills.Construction.ColdStepAtMirrorFrames.ThirdDerivative
variable {ι : Type} [Fintype ι] [DecidableEq ι] {X : Type}
variable {ρ : ℝ} {p : ℝ → ℝ} {m κ : ℝ} {Ψ : BondField ι → ℝ} {K : ι → ι → ℝ} {c₁ W a : ℝ}
  {δ : X → X → ℝ} {loc : ι → X}
theorem LocalizedMeasureHyp.rate_pos (h : LocalizedMeasureHyp ρ p m κ Ψ K c₁ W a δ loc) : 0 < κ := h.measure.rate_pos
theorem localized_weight_nonneg (h : LocalizedMeasureHyp ρ p m κ Ψ K c₁ W a δ loc) (z : X) : 0 ≤ W :=
  (Finset.sum_nonneg fun b _ => expWeight_nonneg _ _ _).trans (h.weight_sum z)
theorem localized_sum_expWeight_le (h : LocalizedMeasureHyp ρ p m κ Ψ K c₁ W a δ loc) {r : ℝ} (hr : κ / 16 ≤ r) (z : X) :
    ∑ b, expWeight δ r (loc b) z ≤ W := sum_expWeight_le_of_le h.site_dist hr h.weight_sum z
theorem localized_placeWeights (h : LocalizedMeasureHyp ρ p m κ Ψ K c₁ W a δ loc) (Y : X) :
    PlaceWeights (fun b => expWeight δ a Y (loc b)) (fun b => expWeight δ (a / 4) Y (loc b)) W := by
  have hκ := h.rate_pos
  have ha := h.rate_le
  refine ⟨fun b => expWeight_nonneg _ _ _, fun b => expWeight_anti h.site_dist (by linarith) _ _, ?_⟩
  have := localized_sum_expWeight_le h (r := a / 4) (by linarith) Y
  simpa only [expWeight_symm h.site_dist _ (loc _) Y] using this
theorem exp_neg_le_mul_exp (h : LocalizedMeasureHyp ρ p m κ Ψ K c₁ W a δ loc) (b₁ b₂ b : ι) :
    Real.exp (-(κ * δ (loc b₁) (loc b₂))) ≤
      Real.exp (-(κ * δ (loc b₁) (loc b))) * Real.exp (κ * δ (loc b) (loc b₂)) := by
  rw [← Real.exp_add]
  apply Real.exp_le_exp.mpr
  have t := h.site_dist.triangle (loc b₁) (loc b₂) (loc b)
  have s := h.site_dist.symm (loc b₂) (loc b)
  have := mul_le_mul_of_nonneg_left t h.rate_pos.le
  rw [s] at this
  linarith
theorem sum_kernel_term_le (h : LocalizedMeasureHyp ρ p m κ Ψ K c₁ W a δ loc) (Y : X) (b : ι) :
    ∑ b₁, ∑ b₂, expWeight δ a Y (loc b₁) * Real.exp (-(κ * δ (loc b₁) (loc b₂))) * K b b₂ ≤
      c₁ * m * (W * expWeight δ (κ / 2) Y (loc b)) := by
  have hκ := h.rate_pos
  have ha := h.rate_le
  have hcm : 0 ≤ c₁ * m := mul_nonneg h.measure.c₁_nonneg (by linarith [h.measure.one_le])
  have in1 : ∀ b₁, ∑ b₂, expWeight δ a Y (loc b₁) * Real.exp (-(κ * δ (loc b₁) (loc b₂))) * K b b₂ ≤
      c₁ * m * (expWeight δ a Y (loc b₁) * expWeight δ κ (loc b₁) (loc b)) := by
    intro b₁
    have s : ∑ b₂, expWeight δ a Y (loc b₁) * Real.exp (-(κ * δ (loc b₁) (loc b₂))) * K b b₂ ≤
        ∑ b₂, expWeight δ a Y (loc b₁) * expWeight δ κ (loc b₁) (loc b) *
          (K b b₂ * Real.exp (κ * δ (loc b) (loc b₂))) := by
      apply Finset.sum_le_sum
      intro b₂ _
      have k0 := convexMeasure_kernel_nonneg h.measure b b₂
      have d := exp_neg_le_mul_exp h b₁ b₂ b
      have w0 := expWeight_nonneg (δ := δ) a Y (loc b₁)
      have := mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left d w0) k0
      refine this.trans (le_of_eq ?_)
      simp only [expWeight]
      ring
    refine s.trans ?_
    rw [← Finset.mul_sum, mul_comm]
    exact mul_le_mul_of_nonneg_right (h.measure.standingConstraints b) (mul_nonneg (expWeight_nonneg _ _ _) (expWeight_nonneg _ _ _))
  refine (Finset.sum_le_sum fun b₁ _ => in1 b₁).trans ?_
  rw [← Finset.mul_sum]
  apply mul_le_mul_of_nonneg_left _ hcm
  exact sum_expWeight_mul_le h.site_dist (by positivity) (by linarith) (by linarith)
    (localized_sum_expWeight_le h (by linarith)) Y (loc b)
theorem sum_ite_term_eq (w : ι → ℝ) (V : ℝ) (b : ι) :
    ∑ b₁, ∑ b₂, w b₁ * Real.exp (-(κ * δ (loc b₁) (loc b₂))) * (if b₂ = b then V else 0) =
      V * ∑ b₁, w b₁ * expWeight δ κ (loc b₁) (loc b) := by
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro b₁ _
  simp only [mul_ite, mul_zero, Finset.sum_ite_eq', Finset.mem_univ, if_true, expWeight]
  ring
theorem byParts_rhs_le (h : LocalizedMeasureHyp ρ p m κ Ψ K c₁ W a δ loc) (Y Y' : X) (b : ι)
    {E Hh N B S o hv hs : ℝ} (hE : 0 ≤ E) (hH : 0 ≤ Hh) (hN : 0 ≤ N) (hB : 0 ≤ B) (hS : 0 ≤ S)
    (ho : 0 ≤ o) (hhv : 0 ≤ hv) (hhs : 0 ≤ hs) :
    m⁻¹ * (∑ b₁, ∑ b₂, (E * expWeight δ a Y (loc b₁)) * Real.exp (-(κ * δ (loc b₁) (loc b₂))) *
          (N * K b b₂ * hv + (if b₂ = b then N * (B + 4) * (hv + hs * o) else 0) +
            (Hh * expWeight δ (a / 4) Y' (loc b₂)) * (N * S))) +
      m⁻¹ * ∑ b₁, ∑ b₂, (Hh * expWeight δ (a / 4) Y' (loc b₁)) * Real.exp (-(κ * δ (loc b₁) (loc b₂))) *
          (N * (E * expWeight δ a Y (loc b) * expWeight δ a Y (loc b₂)) +
            (if b₂ = b then (E * expWeight δ a Y (loc b)) * (N * (1 + o)) else 0)) ≤
      m⁻¹ * (E * N * ((c₁ * m * hv + (B + 4) * (hv + hs * o)) * W * expWeight δ (κ / 2) Y (loc b) +
        Hh * (S * W ^ 2 + W ^ 2 + (1 + o) * W) * expWeight δ (κ / 4) Y Y')) := by
  have hκ := h.rate_pos
  have ha := h.rate_le
  have pl := h.site_dist
  have hm : 0 < m := by linarith [h.measure.one_le]
  have hW : 0 ≤ W := localized_weight_nonneg h Y
  have hmi : 0 ≤ m⁻¹ := inv_nonneg.mpr hm.le
  rw [← mul_add]
  apply mul_le_mul_of_nonneg_left _ hmi
  have e1 : ∀ b₁ b₂, (E * expWeight δ a Y (loc b₁)) * Real.exp (-(κ * δ (loc b₁) (loc b₂))) *
        (N * K b b₂ * hv + (if b₂ = b then N * (B + 4) * (hv + hs * o) else 0) +
          (Hh * expWeight δ (a / 4) Y' (loc b₂)) * (N * S)) =
      (E * N * hv) * (expWeight δ a Y (loc b₁) * Real.exp (-(κ * δ (loc b₁) (loc b₂))) * K b b₂) +
        (E * expWeight δ a Y (loc b₁)) * Real.exp (-(κ * δ (loc b₁) (loc b₂))) *
          (if b₂ = b then N * (B + 4) * (hv + hs * o) else 0) +
        (E * Hh * N * S) * (expWeight δ a Y (loc b₁) * Real.exp (-(κ * δ (loc b₁) (loc b₂))) * expWeight δ (a / 4) Y' (loc b₂)) := by
    intro b₁ b₂
    ring
  have e2 : ∀ b₁ b₂, (Hh * expWeight δ (a / 4) Y' (loc b₁)) * Real.exp (-(κ * δ (loc b₁) (loc b₂))) *
        (N * (E * expWeight δ a Y (loc b) * expWeight δ a Y (loc b₂)) + (if b₂ = b then (E * expWeight δ a Y (loc b)) * (N * (1 + o)) else 0)) =
      (Hh * N * E * expWeight δ a Y (loc b)) * (expWeight δ (a / 4) Y' (loc b₁) * Real.exp (-(κ * δ (loc b₁) (loc b₂))) * expWeight δ a Y (loc b₂)) +
        (Hh * expWeight δ (a / 4) Y' (loc b₁)) * Real.exp (-(κ * δ (loc b₁) (loc b₂))) *
          (if b₂ = b then (E * expWeight δ a Y (loc b)) * (N * (1 + o)) else 0) := by
    intro b₁ b₂
    ring
  simp only [e1, e2, Finset.sum_add_distrib, ← Finset.mul_sum]
  have pa := sum_kernel_term_le h Y b
  have pb : ∑ b₁, expWeight δ a Y (loc b₁) * expWeight δ κ (loc b₁) (loc b) ≤ W * expWeight δ (κ / 2) Y (loc b) :=
    sum_expWeight_mul_le pl (by positivity) (by linarith) (by linarith) (localized_sum_expWeight_le h (by linarith)) Y (loc b)
  have hW4 := fun z => localized_sum_expWeight_le h (r := κ / 16) le_rfl z
  have pc : ∑ b₁, ∑ b₂, expWeight δ a Y (loc b₁) * Real.exp (-(κ * δ (loc b₁) (loc b₂))) * expWeight δ (a / 4) Y' (loc b₂) ≤
      W * (W * expWeight δ (κ / 4) Y Y') := by
    have := sum_sum_expWeight_le pl (κ := κ) (θ₀ := κ / 16) (r₁ := a) (r₂ := a / 4) hκ.le (by linarith)
      (by linarith) (by linarith) hW4 Y Y'
    refine le_trans (le_of_eq ?_) this
    apply Finset.sum_congr rfl
    intro b₁ _
    apply Finset.sum_congr rfl
    intro b₂ _
    rw [expWeight_symm pl _ Y' (loc b₂)]
    rfl
  have pd : ∑ b₁, ∑ b₂, expWeight δ (a / 4) Y' (loc b₁) * Real.exp (-(κ * δ (loc b₁) (loc b₂))) * expWeight δ a Y (loc b₂) ≤
      W * (W * expWeight δ (κ / 4) Y Y') := by
    have := sum_sum_expWeight_le pl (κ := κ) (θ₀ := κ / 16) (r₁ := a / 4) (r₂ := a) hκ.le (by linarith)
      (by linarith) (by linarith) hW4 Y' Y
    rw [expWeight_symm pl _ Y' Y] at this
    refine le_trans (le_of_eq ?_) this
    apply Finset.sum_congr rfl
    intro b₁ _
    apply Finset.sum_congr rfl
    intro b₂ _
    rw [expWeight_symm pl _ Y (loc b₂)]
    rfl
  have pe : ∑ b₁, expWeight δ (a / 4) Y' (loc b₁) * expWeight δ κ (loc b₁) (loc b) ≤ W * expWeight δ (κ / 2) Y' (loc b) :=
    sum_expWeight_mul_le pl (by positivity) (by linarith) (by linarith) (localized_sum_expWeight_le h (by linarith)) Y' (loc b)
  have hwb : expWeight δ a Y (loc b) ≤ 1 := expWeight_le_one pl (by linarith) _ _
  have hwb0 : 0 ≤ expWeight δ a Y (loc b) := expWeight_nonneg _ _ _
  have pf : expWeight δ a Y (loc b) * expWeight δ (κ / 2) Y' (loc b) ≤ expWeight δ (κ / 4) Y Y' := by
    simp only [expWeight]
    rw [← Real.exp_add]
    apply Real.exp_le_exp.mpr
    have t := pl.triangle Y (loc b) Y'
    have s := pl.symm Y' (loc b)
    have n1 := pl.nonneg Y (loc b)
    have n2 := pl.nonneg (loc b) Y'
    rw [s]
    have a1 := mul_le_mul_of_nonneg_right (by linarith : κ / 4 ≤ a) n1
    have a2 := mul_le_mul_of_nonneg_left t (by positivity : 0 ≤ κ / 4)
    nlinarith [mul_nonneg hκ.le n2]
  have qb : ∑ b₁, ∑ b₂, (E * expWeight δ a Y (loc b₁)) * Real.exp (-(κ * δ (loc b₁) (loc b₂))) *
      (if b₂ = b then N * (B + 4) * (hv + hs * o) else 0) =
      (N * (B + 4) * (hv + hs * o)) * ∑ b₁, (E * expWeight δ a Y (loc b₁)) * expWeight δ κ (loc b₁) (loc b) :=
    sum_ite_term_eq _ _ _
  have qe : ∑ b₁, ∑ b₂, (Hh * expWeight δ (a / 4) Y' (loc b₁)) * Real.exp (-(κ * δ (loc b₁) (loc b₂))) *
      (if b₂ = b then (E * expWeight δ a Y (loc b)) * (N * (1 + o)) else 0) =
      ((E * expWeight δ a Y (loc b)) * (N * (1 + o))) * ∑ b₁, (Hh * expWeight δ (a / 4) Y' (loc b₁)) * expWeight δ κ (loc b₁) (loc b) :=
    sum_ite_term_eq _ _ _
  rw [qb, qe]
  set ωb := expWeight δ (κ / 2) Y (loc b) with hωb
  set ω' := expWeight δ (κ / 4) Y Y' with hω'
  have ωb0 : 0 ≤ ωb := expWeight_nonneg _ _ _
  have ω'0 : 0 ≤ ω' := expWeight_nonneg _ _ _
  have A1 := mul_le_mul_of_nonneg_left pa (by positivity : 0 ≤ E * N * hv)
  have pb' : ∑ b₁, (E * expWeight δ a Y (loc b₁)) * expWeight δ κ (loc b₁) (loc b) ≤ E * (W * ωb) := by
    have e : ∑ b₁, (E * expWeight δ a Y (loc b₁)) * expWeight δ κ (loc b₁) (loc b) =
        E * ∑ b₁, expWeight δ a Y (loc b₁) * expWeight δ κ (loc b₁) (loc b) := by
      rw [Finset.mul_sum]
      exact Finset.sum_congr rfl fun b₁ _ => by ring
    rw [e]
    exact mul_le_mul_of_nonneg_left pb hE
  have A2 := mul_le_mul_of_nonneg_left pb' (by positivity : 0 ≤ N * (B + 4) * (hv + hs * o))
  have A3 := mul_le_mul_of_nonneg_left pc (by positivity : 0 ≤ E * Hh * N * S)
  have A4 : Hh * N * E * expWeight δ a Y (loc b) *
      ∑ b₁, ∑ b₂, expWeight δ (a / 4) Y' (loc b₁) * Real.exp (-(κ * δ (loc b₁) (loc b₂))) * expWeight δ a Y (loc b₂) ≤
      Hh * N * E * (W * (W * ω')) := by
    have c0 : 0 ≤ Hh * N * E := by positivity
    have s0 : 0 ≤ ∑ b₁, ∑ b₂, expWeight δ (a / 4) Y' (loc b₁) *
        Real.exp (-(κ * δ (loc b₁) (loc b₂))) * expWeight δ a Y (loc b₂) :=
      Finset.sum_nonneg fun b₁ _ => Finset.sum_nonneg fun b₂ _ =>
        mul_nonneg (mul_nonneg (expWeight_nonneg _ _ _) (Real.exp_pos _).le) (expWeight_nonneg _ _ _)
    have u1 := mul_le_of_le_one_left s0 hwb
    have := mul_le_mul_of_nonneg_left (u1.trans pd) c0
    calc _ = Hh * N * E * (expWeight δ a Y (loc b) * ∑ b₁, ∑ b₂, expWeight δ (a / 4) Y' (loc b₁) *
          Real.exp (-(κ * δ (loc b₁) (loc b₂))) * expWeight δ a Y (loc b₂)) := by ring
      _ ≤ _ := this
  have pe' : ∑ b₁, (Hh * expWeight δ (a / 4) Y' (loc b₁)) * expWeight δ κ (loc b₁) (loc b) ≤
      Hh * (W * expWeight δ (κ / 2) Y' (loc b)) := by
    have e : ∑ b₁, (Hh * expWeight δ (a / 4) Y' (loc b₁)) * expWeight δ κ (loc b₁) (loc b) =
        Hh * ∑ b₁, expWeight δ (a / 4) Y' (loc b₁) * expWeight δ κ (loc b₁) (loc b) := by
      rw [Finset.mul_sum]
      exact Finset.sum_congr rfl fun b₁ _ => by ring
    rw [e]
    exact mul_le_mul_of_nonneg_left pe hH
  have A5 : (E * expWeight δ a Y (loc b)) * (N * (1 + o)) *
      ∑ b₁, (Hh * expWeight δ (a / 4) Y' (loc b₁)) * expWeight δ κ (loc b₁) (loc b) ≤
      E * N * (1 + o) * Hh * W * ω' := by
    have c0 : 0 ≤ (E * expWeight δ a Y (loc b)) * (N * (1 + o)) := by positivity
    have s1 := mul_le_mul_of_nonneg_left pe' c0
    have s2 := mul_le_mul_of_nonneg_left pf (by positivity : 0 ≤ E * N * (1 + o) * Hh * W)
    calc _ ≤ _ := s1
      _ = E * N * (1 + o) * Hh * W * (expWeight δ a Y (loc b) * expWeight δ (κ / 2) Y' (loc b)) := by ring
      _ ≤ _ := s2
  have fin : E * N * hv * (c₁ * m * (W * ωb)) + N * (B + 4) * (hv + hs * o) * (E * (W * ωb)) +
      E * Hh * N * S * (W * (W * ω')) + (Hh * N * E * (W * (W * ω')) + E * N * (1 + o) * Hh * W * ω') =
      E * N * ((c₁ * m * hv + (B + 4) * (hv + hs * o)) * W * ωb +
        Hh * (S * W ^ 2 + W ^ 2 + (1 + o) * W) * ω') := by
    ring
  rw [← fin]
  linarith
end YangMills.Construction.ColdStepAtMirrorFrames.ThirdDerivative
end
noncomputable section
open MeasureTheory Set Filter Topology
namespace YangMills.Construction.ColdStepAtMirrorFrames.ThirdDerivative
variable {ι : Type} [Fintype ι] [DecidableEq ι] {X : Type}
variable {ρ : ℝ} {p : ℝ → ℝ} {m κ : ℝ} {Ψ : BondField ι → ℝ} {K : ι → ι → ℝ} {c₁ W a : ℝ}
  {δ : X → X → ℝ} {loc : ι → X}
theorem ballL2Norm_centered_le_of_grad (hCov : BallCovarianceBound) {d : ι → ι → ℝ}
    (h : ConvexMeasureHyp ρ p m κ d Ψ K c₁ W) {f : BondField ι → ℝ} (hf : ContDiff ℝ 1 f)
    {F W' : ℝ} {wq : ι → ℝ} (hF : 0 ≤ F) (hwq : ∀ b, 0 ≤ wq b) (hsum : ∑ b, wq b ≤ W')
    (hpn : ∀ b η, InOpenBalls ρ η → bondGradNorm f b η ≤ F * wq b) :
    ballL2Norm (extendedCutoff ρ p) Ψ (fun η => f η - ballExpectation (extendedCutoff ρ p) Ψ f) ≤
      F * W' / Real.sqrt m := by
  have hd := h.data
  have hm : 0 < m := by linarith [h.one_le]
  have cf := hf.continuous
  set mf := ballExpectation (extendedCutoff ρ p) Ψ f with hmf
  have hW' : 0 ≤ W' := (Finset.sum_nonneg fun b _ => hwq b).trans hsum
  have hnorm : ∀ b, ballL2Norm (extendedCutoff ρ p) Ψ (bondGradNorm f b) ≤ F * wq b := fun b =>
    ballL2Norm_le_const hd (bondGradNorm_continuous hf b) (mul_nonneg hF (hwq b)) fun η hη => by
      rw [abs_of_nonneg (bondGradNorm_nonneg _ _ _)]
      exact hpn b η hη
  have t := abs_ballCovariance_le_of_sup hCov h.pos hm h.rate_pos.le h.cutoff h.dist h.convex hd hf hf hpn hnorm
  have hs : ∑ b, ∑ b', F * wq b * Real.exp (-(κ * d b b')) * (F * wq b') ≤ (F * W') ^ 2 := by
    have k1 : ∀ b b', F * wq b * Real.exp (-(κ * d b b')) * (F * wq b') ≤
        (F * wq b) * (F * wq b') := by
      intro b b'
      have e1 : Real.exp (-(κ * d b b')) ≤ 1 := by
        apply Real.exp_le_one_iff.mpr
        have := mul_nonneg h.rate_pos.le (pseudoMetric_nonneg h.dist b b')
        linarith
      have c0 := mul_nonneg hF (hwq b)
      have c1 := mul_nonneg hF (hwq b')
      exact mul_le_mul_of_nonneg_right (mul_le_of_le_one_right c0 e1) c1
    refine (Finset.sum_le_sum fun b _ => Finset.sum_le_sum fun b' _ => k1 b b').trans ?_
    have e : ∑ b, ∑ b', (F * wq b) * (F * wq b') = (F * ∑ b, wq b) * (F * ∑ b, wq b) := by
      rw [Finset.mul_sum, Finset.sum_mul]
      apply Finset.sum_congr rfl
      intro b _
      rw [Finset.mul_sum]
    rw [e, sq]
    have s0 : 0 ≤ ∑ b, wq b := Finset.sum_nonneg fun b _ => hwq b
    have s1 := mul_le_mul_of_nonneg_left hsum hF
    exact mul_le_mul s1 s1 (mul_nonneg hF s0) (mul_nonneg hF hW')
  have hcov : ballCovariance (extendedCutoff ρ p) Ψ f f ≤ (F * W') ^ 2 / m := by
    have := (le_abs_self _).trans t
    refine this.trans ?_
    rw [div_eq_inv_mul]
    exact mul_le_mul_of_nonneg_left hs (inv_nonneg.mpr hm.le)
  have hmean : ballExpectation (extendedCutoff ρ p) Ψ (fun η => (f η - mf) ^ 2) =
      ballCovariance (extendedCutoff ρ p) Ψ f f := by
    rw [ballCovariance_eq hd cf cf]
    have e : (fun η => (f η - mf) ^ 2) = fun η => (f η - mf) * f η - mf * (f η - mf) := by
      funext η
      ring
    have c1 : Continuous fun η => f η - mf := cf.sub continuous_const
    rw [e, ballExpectation_sub hd (f := fun η => (f η - mf) * f η) (g := fun η => mf * (f η - mf))
      (by fun_prop) (by fun_prop), ballExpectation_const_mul, ballExpectation_sub hd cf continuous_const, ballExpectation_const hd]
    simp [hmf]
  unfold ballL2Norm
  rw [hmean, ← Real.sqrt_sq (by positivity : 0 ≤ F * W'), ← Real.sqrt_div (sq_nonneg _)]
  exact Real.sqrt_le_sqrt hcov
theorem byParts_rhs_numbers {s m c₁ W cB cs co E N Hh ωb ω' : ℝ} (hs : 1 ≤ s) (hm : m = s ^ 2)
    (hc₁ : 0 ≤ c₁) (hW : 0 ≤ W) (hcB : 0 ≤ cB) (hcs : 0 ≤ cs) (hco : 0 ≤ co) (hE : 0 ≤ E)
    (hN : 0 ≤ N) (hH : 0 ≤ Hh) (hωb : 0 ≤ ωb) (hω' : 0 ≤ ω') :
    m⁻¹ * (E * N * ((c₁ * m * (Hh * W / s) + (cB * m + 4) * (Hh * W / s + Hh * (co / s))) * W * ωb +
        Hh * ((cs * s + 1 + co / s) * W ^ 2 + W ^ 2 + (1 + co / s) * W) * ω')) ≤
      (c₁ * W ^ 2 + (cB + 4) * (W + co) * W + (cs + 1 + co) * W ^ 2 + W ^ 2 + (1 + co) * W) *
        (N * Hh * E / s) * (ωb + ω') := by
  have s0 : 0 < s := by linarith
  have hm0 : 0 < m := by rw [hm]; positivity
  have hinv : (1 : ℝ) / s ≤ 1 := by
    rw [div_le_one s0]
    exact hs
  have P : 0 ≤ N * Hh * E / s := by positivity
  have e1 : m⁻¹ * (E * N * (c₁ * m * (Hh * W / s) * W * ωb)) = c₁ * W ^ 2 * (N * Hh * E / s) * ωb := by
    rw [hm]
    field_simp
  have i2 : m⁻¹ * (cB * m + 4) ≤ cB + 4 := by
    have : m⁻¹ ≤ 1 := by
      rw [hm]
      apply inv_le_one_of_one_le₀
      nlinarith
    have e : m⁻¹ * (cB * m + 4) = cB + 4 * m⁻¹ := by
      field_simp
    rw [e]
    linarith
  have e2 : m⁻¹ * (E * N * ((cB * m + 4) * (Hh * W / s + Hh * (co / s)) * W * ωb)) =
      (m⁻¹ * (cB * m + 4)) * ((W + co) * W * (N * Hh * E / s) * ωb) := by
    field_simp
  have i3 : 0 ≤ (W + co) * W * (N * Hh * E / s) * ωb := by positivity
  have t2 := mul_le_mul_of_nonneg_right i2 i3
  have i4 : m⁻¹ * (cs * s + 1 + co / s) ≤ (cs + 1 + co) / s := by
    have h1 : cs * s + 1 + co / s ≤ (cs + 1 + co) * s := by
      have a1 : co / s ≤ co := by
        have := mul_le_mul_of_nonneg_left hinv hco
        calc co / s = co * (1 / s) := by ring
          _ ≤ co * 1 := this
          _ = co := by ring
      nlinarith
    have h2 : m⁻¹ * ((cs + 1 + co) * s) = (cs + 1 + co) / s := by
      rw [hm]
      field_simp
    rw [← h2]
    exact mul_le_mul_of_nonneg_left h1 (inv_nonneg.mpr hm0.le)
  have i5 : m⁻¹ ≤ 1 / s := by
    rw [hm, one_div]
    apply inv_anti₀ s0
    nlinarith
  have i6 : m⁻¹ * (1 + co / s) ≤ (1 + co) / s := by
    have h1 : 1 + co / s ≤ 1 + co := by
      have := mul_le_mul_of_nonneg_left hinv hco
      have e : co / s = co * (1 / s) := by ring
      rw [e]
      linarith
    have h2 := mul_le_mul_of_nonneg_left h1 (inv_nonneg.mpr hm0.le)
    have h3 := mul_le_mul_of_nonneg_right i5 (by positivity : 0 ≤ 1 + co)
    have e : 1 / s * (1 + co) = (1 + co) / s := by ring
    linarith
  have base : 0 ≤ N * Hh * E * ω' := by positivity
  have t3 : m⁻¹ * (E * N * (Hh * ((cs * s + 1 + co / s) * W ^ 2 + W ^ 2 + (1 + co / s) * W) * ω')) ≤
      ((cs + 1 + co) * W ^ 2 + W ^ 2 + (1 + co) * W) * (N * Hh * E / s) * ω' := by
    have e : m⁻¹ * (E * N * (Hh * ((cs * s + 1 + co / s) * W ^ 2 + W ^ 2 + (1 + co / s) * W) * ω')) =
        (m⁻¹ * (cs * s + 1 + co / s) * W ^ 2 + m⁻¹ * W ^ 2 + m⁻¹ * (1 + co / s) * W) * (N * Hh * E * ω') := by
      ring
    rw [e]
    have f1 := mul_le_mul_of_nonneg_right i4 (sq_nonneg W)
    have f2 := mul_le_mul_of_nonneg_right i5 (sq_nonneg W)
    have f3 := mul_le_mul_of_nonneg_right i6 hW
    have f4 : m⁻¹ * (cs * s + 1 + co / s) * W ^ 2 + m⁻¹ * W ^ 2 + m⁻¹ * (1 + co / s) * W ≤
        ((cs + 1 + co) * W ^ 2 + W ^ 2 + (1 + co) * W) / s := by
      have e2 : ((cs + 1 + co) * W ^ 2 + W ^ 2 + (1 + co) * W) / s =
          (cs + 1 + co) / s * W ^ 2 + 1 / s * W ^ 2 + (1 + co) / s * W := by ring
      rw [e2]
      linarith
    have := mul_le_mul_of_nonneg_right f4 base
    refine this.trans (le_of_eq ?_)
    ring
  have split : m⁻¹ * (E * N * ((c₁ * m * (Hh * W / s) + (cB * m + 4) * (Hh * W / s + Hh * (co / s))) * W * ωb +
        Hh * ((cs * s + 1 + co / s) * W ^ 2 + W ^ 2 + (1 + co / s) * W) * ω')) =
      m⁻¹ * (E * N * (c₁ * m * (Hh * W / s) * W * ωb)) +
        m⁻¹ * (E * N * ((cB * m + 4) * (Hh * W / s + Hh * (co / s)) * W * ωb)) +
        m⁻¹ * (E * N * (Hh * ((cs * s + 1 + co / s) * W ^ 2 + W ^ 2 + (1 + co / s) * W) * ω')) := by
    ring
  rw [split, e1, e2]
  set Bs := N * Hh * E / s with hBs
  have fin : (c₁ * W ^ 2 + (cB + 4) * (W + co) * W + (cs + 1 + co) * W ^ 2 + W ^ 2 + (1 + co) * W) *
        Bs * (ωb + ω') =
      c₁ * W ^ 2 * Bs * ωb + (cB + 4) * ((W + co) * W * Bs * ωb) +
        ((cs + 1 + co) * W ^ 2 + W ^ 2 + (1 + co) * W) * Bs * ω' +
        (c₁ * W ^ 2 * (Bs * ω') + (cB + 4) * (W + co) * W * (Bs * ω') +
          ((cs + 1 + co) * W ^ 2 + W ^ 2 + (1 + co) * W) * (Bs * ωb)) := by
    ring
  rw [fin]
  have q0 : 0 ≤ c₁ * W ^ 2 * (Bs * ω') + (cB + 4) * (W + co) * W * (Bs * ω') +
      ((cs + 1 + co) * W ^ 2 + W ^ 2 + (1 + co) * W) * (Bs * ωb) := by positivity
  linarith
end YangMills.Construction.ColdStepAtMirrorFrames.ThirdDerivative
end
noncomputable section
open MeasureTheory Set Filter Topology
namespace YangMills.Construction.ColdStepAtMirrorFrames.ThirdDerivative
variable {ι : Type} [Fintype ι] [DecidableEq ι] {X : Type}
variable {ρ : ℝ} {p : ℝ → ℝ} {m κ : ℝ} {Ψ : BondField ι → ℝ} {K : ι → ι → ℝ} {c₁ W a : ℝ}
  {δ : X → X → ℝ} {loc : ι → X}
def byPartsConst (ρ c₁ W co : ℝ) : ℝ :=
  c₁ * W ^ 2 + ((1 + ρ * c₁) + 4) * (W + co) * W + ((1 + c₁ * Real.sqrt (8 * W)) + 1 + co) * W ^ 2 +
    W ^ 2 + (1 + co) * W
theorem expWeight_decay_cases (pl : IsSiteDistance δ) (hκ : 0 < κ) (ha : 4 * κ ≤ a) (Y Y' Z : X) :
    expWeight δ (a / 4) Y' Z ≤ Real.exp (-(κ / 8 * (δ Y Y' + δ Y' Z))) ∨
      expWeight δ (κ / 2) Y Z + expWeight δ (κ / 4) Y Y' ≤ 2 * Real.exp (-(κ / 8 * (δ Y Y' + δ Y' Z))) := by
  set t := δ Y Y' + δ Y' Z with ht
  have n1 := pl.nonneg Y Y'
  have n2 := pl.nonneg Y' Z
  rcases le_or_gt t (4 * δ Y' Z) with h | h
  · left
    apply Real.exp_le_exp.mpr
    have : κ * δ Y' Z ≤ a / 4 * δ Y' Z := mul_le_mul_of_nonneg_right (by linarith) n2
    nlinarith [mul_le_mul_of_nonneg_left h hκ.le]
  · right
    have t1 := pl.triangle Y Z Y'
    have t2 := pl.symm Z Y'
    have g1 : t / 2 ≤ δ Y Z := by
      rw [t2] at t1
      simp only [ht] at h ⊢
      linarith
    have g2 : 3 * t / 4 ≤ δ Y Y' := by
      simp only [ht] at h ⊢
      linarith
    have a1 : expWeight δ (κ / 2) Y Z ≤ Real.exp (-(κ / 8 * t)) := by
      apply Real.exp_le_exp.mpr
      have ht0 : 0 ≤ t := by simp only [ht]; positivity
      nlinarith [mul_le_mul_of_nonneg_left g1 hκ.le, mul_nonneg hκ.le ht0]
    have a2 : expWeight δ (κ / 4) Y Y' ≤ Real.exp (-(κ / 8 * t)) := by
      apply Real.exp_le_exp.mpr
      have ht0 : 0 ≤ t := by simp only [ht]; positivity
      nlinarith [mul_le_mul_of_nonneg_left g2 hκ.le, mul_nonneg hκ.le ht0]
    linarith
theorem fderiv_bondPartialDeriv_apply {g : BondField ι → ℝ} (hg : ContDiff ℝ 2 g) (b b' : ι)
    (e e' : BondVector) (η : BondField ι) :
    fderiv ℝ (fun ζ => bondPartialDeriv g b ζ e) η (bondVariation b' e') =
      fderiv ℝ (fderiv ℝ g) η (bondVariation b' e') (bondVariation b e) := by
  have hd : HasFDerivAt (fderiv ℝ g) (fderiv ℝ (fderiv ℝ g) η) η :=
    ((hg.fderiv_right (m := 1) (by norm_num)).differentiable (by norm_num) η).hasFDerivAt
  have h1 := hd.clm_apply (hasFDerivAt_const (bondVariation b e) η)
  have h2 : fderiv ℝ (fun ζ => bondPartialDeriv g b ζ e) η = _ := h1.fderiv
  rw [h2]
  simp
theorem abs_ballCovariance_bondTerm_decay (hCov : BallCovarianceBound)
    (hMom : GaussianMomentBound) (hR : CutoffFactorIsRadialCutoff)
    (h : LocalizedMeasureHyp ρ p m κ Ψ K c₁ W a δ loc) {c co : ℝ} (hc : RimBoundConst ρ p c) (hco : 0 ≤ co)
    (ho : ∀ (b : ι) (ε : ℝ), 0 < ε →
      ballL2Norm (extendedCutoff ρ p) Ψ (fun η => rimBound ρ p c ε ‖η b‖) ≤ co / Real.sqrt m)
    {g H : BondField ι → ℝ} {E E₃ Hh : ℝ} {Y Y' : X} (hE : 0 ≤ E)
    (hg : ThirdJetBound ρ g E E₃ (fun b => expWeight δ a Y (loc b))) (hH : ContDiff ℝ 1 H) (hHh : 0 ≤ Hh)
    (hHd : ∀ b' η, InOpenBalls ρ η → bondGradNorm H b' η ≤ Hh * expWeight δ (a / 4) Y' (loc b'))
    (hsup : ∀ η, InOpenBalls ρ η → 2 * |H η| ≤ Hh) (b : ι) {e : BondVector} (he : ‖e‖ = 1)
    {α : BondVector → ℝ} (hα : ContDiff ℝ 2 α) {N : ℝ} (hN : 0 ≤ N)
    (h0 : ∀ v : BondVector, ‖v‖ < ρ → |α v| ≤ N) (h1 : ∀ v : BondVector, ‖v‖ < ρ → ‖fderiv ℝ α v‖ ≤ N)
    (h2 : ∀ v : BondVector, ‖v‖ < ρ → ‖fderiv ℝ (fderiv ℝ α) v‖ ≤ N) :
    |ballCovariance (extendedCutoff ρ p) Ψ g (fun η => α (η b) * bondPartialDeriv H b η e)| ≤
      (W + 2 * byPartsConst ρ c₁ W co) * (N * Hh * E / Real.sqrt m) *
        Real.exp (-(κ / 8 * (δ Y Y' + δ Y' (loc b)))) := by
  have mc := h.measure
  have hd := mc.data
  have hρ := mc.pos
  have hκ := h.rate_pos
  have pl := h.site_dist
  have hm1 := mc.one_le
  have hm0 : 0 < m := by linarith
  have hW : 0 ≤ W := localized_weight_nonneg h Y
  have hc₁ := mc.c₁_nonneg
  set s := Real.sqrt m with hs
  have hs1 : 1 ≤ s := by
    rw [hs]
    exact Real.one_le_sqrt.mpr hm1
  have hms : m = s ^ 2 := (Real.sq_sqrt hm0.le).symm
  have hg2 : ContDiff ℝ 2 g := hg.smooth.of_le (by norm_num)
  have hg1 : ContDiff ℝ 1 g := hg.smooth.of_le (by norm_num)
  have BC : OneBondHyp ρ p m κ (fun b b' => δ (loc b) (loc b')) Ψ K b e α N c
      ((1 + ρ * c₁) * m) ((1 + c₁ * Real.sqrt (8 * W)) * s) (co / s) := by
    refine ⟨hρ, mc.cutoff, hm0, hκ.le, mc.dist, mc.convex, hd, he, hα, hN, h0, h1, h2, hc, ?_,
      ballL2Norm_bondPartialDeriv_le hMom hR mc b e he, fun ε hε => ho b ε hε⟩
    intro η hη
    have := abs_bondPartialDeriv_le mc b e η hη
    rwa [he, mul_one] at this
  have hA : ∀ b' η, InOpenBalls ρ η → bondGradNorm g b' η ≤ E * expWeight δ a Y (loc b') := by
    intro b' η hη
    apply bondGradNorm_le (mul_nonneg hE (expWeight_nonneg _ _ _))
    intro e'
    exact hg.first η hη b' e'
  have hGe : ∀ b' η, InOpenBalls ρ η → bondGradNorm (fun ζ => bondPartialDeriv g b ζ e) b' η ≤
      E * expWeight δ a Y (loc b) * expWeight δ a Y (loc b') := by
    intro b' η hη
    apply bondGradNorm_le (mul_nonneg (mul_nonneg hE (expWeight_nonneg _ _ _)) (expWeight_nonneg _ _ _))
    intro e'
    rw [fderiv_bondPartialDeriv_apply hg2]
    have := hg.second η hη b' b e' e
    rw [he, mul_one] at this
    refine this.trans (le_of_eq ?_)
    ring
  have wq := localized_placeWeights h Y'
  have hhv : ballL2Norm (extendedCutoff ρ p) Ψ (fun η => H η - ballExpectation (extendedCutoff ρ p) Ψ H) ≤
      Hh * W / s :=
    ballL2Norm_centered_le_of_grad hCov mc hH hHh (fun b => (expWeight_nonneg _ _ _)) wq.sum hHd
  have hhs : ∀ η, InOpenBalls ρ η → |H η - ballExpectation (extendedCutoff ρ p) Ψ H| ≤ Hh := by
    intro η hη
    have a1 : |ballExpectation (extendedCutoff ρ p) Ψ H| ≤ Hh / 2 :=
      (abs_ballExpectation_le_ballL2Norm hd hH.continuous).trans (ballL2Norm_le_const hd hH.continuous (by positivity)
        fun ζ hζ => by linarith [hsup ζ hζ])
    have a2 := hsup η hη
    have := abs_sub (H η) (ballExpectation (extendedCutoff ρ p) Ψ H)
    linarith
  have bp := abs_ballCovariance_bondTerm_le hCov hR BC hg2 hH hA hHd hGe hhv hhs
  have r := byParts_rhs_le h Y Y' b (E := E) (Hh := Hh) (N := N) (B := (1 + ρ * c₁) * m)
    (S := (1 + c₁ * Real.sqrt (8 * W)) * s + 1 + co / s) (o := co / s) (hv := Hh * W / s) (hs := Hh)
    hE hHh hN (by positivity) (by positivity) (by positivity) (by positivity) hHh
  have n := byParts_rhs_numbers (c₁ := c₁) (W := W) (cB := 1 + ρ * c₁) (cs := 1 + c₁ * Real.sqrt (8 * W))
    (co := co) (E := E) (N := N) (Hh := Hh) (ωb := expWeight δ (κ / 2) Y (loc b))
    (ω' := expWeight δ (κ / 4) Y Y') hs1 hms hc₁ hW (by positivity) (by positivity) hco hE hN hHh
    (expWeight_nonneg _ _ _) (expWeight_nonneg _ _ _)
  have D2 : |ballCovariance (extendedCutoff ρ p) Ψ g (fun η => α (η b) * bondPartialDeriv H b η e)| ≤
      byPartsConst ρ c₁ W co * (N * Hh * E / s) * (expWeight δ (κ / 2) Y (loc b) + expWeight δ (κ / 4) Y Y') :=
    bp.trans (r.trans n)
  have cα : Continuous fun η : BondField ι => α (η b) * bondPartialDeriv H b η e :=
    (hα.continuous.comp (continuous_apply b)).mul (bondPartialDeriv_continuous hH b e)
  have wg := localized_placeWeights h Y
  have hgv : ballL2Norm (extendedCutoff ρ p) Ψ (fun η => g η - ballExpectation (extendedCutoff ρ p) Ψ g) ≤
      E * W / s := by
    refine ballL2Norm_centered_le_of_grad hCov mc hg1 hE (fun b => expWeight_nonneg _ _ _) wg.sum fun b' η hη => ?_
    refine (hA b' η hη).trans ?_
    exact mul_le_mul_of_nonneg_left (wg.le b') hE
  have hF : ballL2Norm (extendedCutoff ρ p) Ψ (fun η => α (η b) * bondPartialDeriv H b η e) ≤
      N * (Hh * expWeight δ (a / 4) Y' (loc b)) := by
    refine ballL2Norm_le_const hd cα (by have := expWeight_nonneg (δ := δ) (a / 4) Y' (loc b); positivity) ?_
    intro η hη
    rw [abs_mul]
    have e1 := abs_fderiv_bondVariation_le H b η e
    rw [he, mul_one] at e1
    exact mul_le_mul (h0 _ (hη b)) (e1.trans (hHd b η hη)) (abs_nonneg _) hN
  have D1 : |ballCovariance (extendedCutoff ρ p) Ψ g (fun η => α (η b) * bondPartialDeriv H b η e)| ≤
      W * (N * Hh * E / s) * expWeight δ (a / 4) Y' (loc b) := by
    rw [ballCovariance_eq hd hg1.continuous cα]
    refine (abs_ballExpectation_mul_le hd (hg1.continuous.sub continuous_const) cα).trans ?_
    refine (mul_le_mul hgv hF (ballL2Norm_nonneg _) (by positivity)).trans (le_of_eq ?_)
    ring
  set Bs := N * Hh * E / s with hBs
  have hC3 : 0 ≤ byPartsConst ρ c₁ W co := by
    unfold byPartsConst
    positivity
  set T := Real.exp (-(κ / 8 * (δ Y Y' + δ Y' (loc b)))) with hT
  have hT0 : 0 ≤ T := (Real.exp_pos _).le
  have hc0 : 0 ≤ W * Bs := by positivity
  have hc1 : 0 ≤ byPartsConst ρ c₁ W co * Bs := by positivity
  rcases expWeight_decay_cases pl hκ h.rate_le Y Y' (loc b) with hq | hq
  · have := mul_le_mul_of_nonneg_left hq hc0
    have e : (W + 2 * byPartsConst ρ c₁ W co) * Bs * T = W * Bs * T + 2 * (byPartsConst ρ c₁ W co * Bs * T) := by ring
    rw [e]
    have := mul_nonneg hc1 hT0
    linarith
  · have := mul_le_mul_of_nonneg_left hq hc1
    have e : (W + 2 * byPartsConst ρ c₁ W co) * Bs * T = W * Bs * T + byPartsConst ρ c₁ W co * Bs * (2 * T) := by ring
    rw [e]
    have := mul_nonneg hc0 hT0
    linarith
end YangMills.Construction.ColdStepAtMirrorFrames.ThirdDerivative
end
noncomputable section
open MeasureTheory Set Filter Topology
namespace YangMills.Construction.ColdStepAtMirrorFrames.ThirdDerivative
variable {ι : Type} [Fintype ι] [DecidableEq ι] {X : Type}
variable {ρ : ℝ} {p : ℝ → ℝ} {m κ : ℝ} {Ψ : BondField ι → ℝ} {K : ι → ι → ℝ} {c₁ W a : ℝ}
  {δ : X → X → ℝ} {loc : ι → X}
theorem bondGradNorm_sub_le {f g : BondField ι → ℝ} (hf : ContDiff ℝ 1 f) (hg : ContDiff ℝ 1 g)
    (b : ι) (η : BondField ι) :
    bondGradNorm (fun ζ => f ζ - g ζ) b η ≤ bondGradNorm f b η + bondGradNorm g b η := by
  apply bondGradNorm_le (add_nonneg (bondGradNorm_nonneg _ _ _) (bondGradNorm_nonneg _ _ _))
  intro e
  have h1 := ((hf.differentiable (by norm_num)) η).hasFDerivAt
  have h2 := ((hg.differentiable (by norm_num)) η).hasFDerivAt
  have h3 : fderiv ℝ (fun ζ => f ζ - g ζ) η = _ := (h1.sub h2).fderiv
  rw [h3]
  simp only [_root_.sub_apply]
  have a1 := abs_fderiv_bondVariation_le f b η e
  have a2 := abs_fderiv_bondVariation_le g b η e
  have := abs_sub (fderiv ℝ f η (bondVariation b e)) (fderiv ℝ g η (bondVariation b e))
  nlinarith
theorem ballCovariance_add (hd : IsCutoffMeasureData ρ (extendedCutoff ρ p) Ψ) {g h₁ h₂ : BondField ι → ℝ}
    (hg : Continuous g) (c₁' : Continuous h₁) (c₂ : Continuous h₂) :
    ballCovariance (extendedCutoff ρ p) Ψ g (fun η => h₁ η + h₂ η) =
      ballCovariance (extendedCutoff ρ p) Ψ g h₁ + ballCovariance (extendedCutoff ρ p) Ψ g h₂ := by
  have c3 : Continuous fun η => h₁ η + h₂ η := c₁'.add c₂
  rw [ballCovariance_eq hd hg c3, ballCovariance_eq hd hg c₁', ballCovariance_eq hd hg c₂]
  have cg : Continuous fun η => g η - ballExpectation (extendedCutoff ρ p) Ψ g := hg.sub continuous_const
  have e : (fun η => (g η - ballExpectation (extendedCutoff ρ p) Ψ g) * (h₁ η + h₂ η)) =
      fun η => (g η - ballExpectation (extendedCutoff ρ p) Ψ g) * h₁ η +
        (g η - ballExpectation (extendedCutoff ρ p) Ψ g) * h₂ η := by
    funext η
    ring
  rw [e]
  exact ballExpectation_add hd (cg.mul c₁') (cg.mul c₂)
theorem ballCovariance_sum (hd : IsCutoffMeasureData ρ (extendedCutoff ρ p) Ψ) {κ' : Type} {s : Finset κ'}
    {g : BondField ι → ℝ} {f : κ' → BondField ι → ℝ} (hg : Continuous g)
    (hf : ∀ i, Continuous (f i)) :
    ballCovariance (extendedCutoff ρ p) Ψ g (fun η => ∑ i ∈ s, f i η) =
      ∑ i ∈ s, ballCovariance (extendedCutoff ρ p) Ψ g (f i) := by
  classical
  induction s using Finset.induction_on with
  | empty =>
    simp only [Finset.sum_empty]
    rw [ballCovariance_eq hd hg continuous_const]
    simp only [mul_zero]
    exact ballExpectation_const hd 0
  | insert a s ha ih =>
    simp only [Finset.sum_insert ha]
    have c2 : Continuous fun η => ∑ i ∈ s, f i η := continuous_finsetSum _ fun i _ => hf i
    rw [ballCovariance_add hd hg (hf a) c2, ih]
theorem isAdmissible_one (pl : IsSiteDistance δ) {a : ℝ} (ha : 0 ≤ a) (Y c : X) {k : ℝ} (hk : 0 ≤ k) :
    IsAdmissible (fun b => expWeight δ a Y (loc b)) (fun b => expWeight δ (a / 4) Y (loc b))
      (fun b => k * expWeight δ a (loc b) c) (k * expWeight δ (a / 4) Y c) := by
  intro b
  have key : expWeight δ a Y (loc b) * expWeight δ a (loc b) c ≤ expWeight δ (a / 4) Y c * expWeight δ (a / 4) Y (loc b) := by
    simp only [expWeight]
    rw [← Real.exp_add, ← Real.exp_add]
    apply Real.exp_le_exp.mpr
    have t := pl.triangle Y (loc b) c
    have n1 := pl.nonneg Y (loc b)
    have n2 := pl.nonneg (loc b) c
    nlinarith [mul_le_mul_of_nonneg_left t ha, mul_nonneg ha n1, mul_nonneg ha n2]
  have := mul_le_mul_of_nonneg_left key hk
  calc _ = k * (expWeight δ a Y (loc b) * expWeight δ a (loc b) c) := by ring
    _ ≤ _ := this
    _ = _ := by ring
theorem isAdmissible_two (pl : IsSiteDistance δ) {a : ℝ} (ha : 0 ≤ a) (Y c c' : X) {k : ℝ} (hk : 0 ≤ k) :
    IsAdmissible (fun b => expWeight δ a Y (loc b)) (fun b => expWeight δ (a / 4) Y (loc b))
      (fun b => k * (expWeight δ a (loc b) c * expWeight δ a (loc b) c'))
      (k * (expWeight δ (a / 4) Y c * expWeight δ (a / 4) Y c')) := by
  intro b
  have key : expWeight δ a Y (loc b) * (expWeight δ a (loc b) c * expWeight δ a (loc b) c') ≤
      (expWeight δ (a / 4) Y c * expWeight δ (a / 4) Y c') * expWeight δ (a / 4) Y (loc b) := by
    simp only [expWeight]
    rw [← Real.exp_add, ← Real.exp_add, ← Real.exp_add, ← Real.exp_add]
    apply Real.exp_le_exp.mpr
    have t := pl.triangle Y (loc b) c
    have t' := pl.triangle Y (loc b) c'
    have n1 := pl.nonneg Y (loc b)
    have n2 := pl.nonneg (loc b) c
    have n3 := pl.nonneg (loc b) c'
    nlinarith [mul_le_mul_of_nonneg_left t ha, mul_le_mul_of_nonneg_left t' ha, mul_nonneg ha n1,
      mul_nonneg ha n2, mul_nonneg ha n3]
  have := mul_le_mul_of_nonneg_left key hk
  calc _ = k * (expWeight δ a Y (loc b) * (expWeight δ a (loc b) c * expWeight δ a (loc b) c')) := by ring
    _ ≤ _ := this
    _ = _ := by ring
theorem isAdmissible_three (pl : IsSiteDistance δ) {a : ℝ} (ha : 0 ≤ a) (Y c c' c'' : X) {k : ℝ}
    (hk : 0 ≤ k) :
    IsAdmissible (fun b => expWeight δ a Y (loc b)) (fun b => expWeight δ (a / 4) Y (loc b))
      (fun b => k * (expWeight δ a (loc b) c * expWeight δ a (loc b) c' * expWeight δ a (loc b) c''))
      (k * (expWeight δ (a / 4) Y c * expWeight δ (a / 4) Y c' * expWeight δ (a / 4) Y c'')) := by
  intro b
  have key : expWeight δ a Y (loc b) * (expWeight δ a (loc b) c * expWeight δ a (loc b) c' * expWeight δ a (loc b) c'') ≤
      (expWeight δ (a / 4) Y c * expWeight δ (a / 4) Y c' * expWeight δ (a / 4) Y c'') * expWeight δ (a / 4) Y (loc b) := by
    simp only [expWeight]
    rw [← Real.exp_add, ← Real.exp_add, ← Real.exp_add, ← Real.exp_add, ← Real.exp_add,
      ← Real.exp_add]
    apply Real.exp_le_exp.mpr
    have t := pl.triangle Y (loc b) c
    have t' := pl.triangle Y (loc b) c'
    have t'' := pl.triangle Y (loc b) c''
    have n1 := pl.nonneg Y (loc b)
    have n2 := pl.nonneg (loc b) c
    have n3 := pl.nonneg (loc b) c'
    have n4 := pl.nonneg (loc b) c''
    nlinarith [mul_le_mul_of_nonneg_left t ha, mul_le_mul_of_nonneg_left t' ha,
      mul_le_mul_of_nonneg_left t'' ha, mul_nonneg ha n1, mul_nonneg ha n2, mul_nonneg ha n3,
      mul_nonneg ha n4]
  have := mul_le_mul_of_nonneg_left key hk
  calc _ = k * (expWeight δ a Y (loc b) * (expWeight δ a (loc b) c * expWeight δ a (loc b) c' * expWeight δ a (loc b) c'')) := by
        ring
    _ ≤ _ := this
    _ = _ := by ring
theorem coord_bounds {z : BondVector → BondVector} (hz : ContDiff ℝ 2 z) (i : Fin 3) (v : BondVector) :
    |(z v) i| ≤ ‖z v‖ ∧
      ‖fderiv ℝ (fun w => (z w) i) v‖ ≤ ‖fderiv ℝ z v‖ ∧
      ‖fderiv ℝ (fderiv ℝ (fun w => (z w) i)) v‖ ≤ ‖fderiv ℝ (fderiv ℝ z) v‖ := by
  set P : BondVector →L[ℝ] ℝ := EuclideanSpace.proj i with hP
  have hP1 : ‖P‖ ≤ 1 := by
    apply ContinuousLinearMap.opNorm_le_bound _ zero_le_one
    intro w
    simp only [hP, one_mul]
    exact PiLp.norm_apply_le w i
  have hd1 : ∀ w, HasFDerivAt z (fderiv ℝ z w) w := fun w =>
    ((hz.differentiable (by norm_num)) w).hasFDerivAt
  have e1 : ∀ w, fderiv ℝ (fun w => (z w) i) w = P.comp (fderiv ℝ z w) := fun w =>
    (P.hasFDerivAt.comp w (hd1 w)).fderiv
  refine ⟨?_, ?_, ?_⟩
  · have := PiLp.norm_apply_le (z v) i
    simpa using this
  · rw [e1]
    refine (ContinuousLinearMap.opNorm_comp_le _ _).trans ?_
    have := norm_nonneg (fderiv ℝ z v)
    nlinarith
  · have e2 : fderiv ℝ (fun w => (z w) i) = fun w => P.comp (fderiv ℝ z w) := funext e1
    rw [e2]
    have hd2 : HasFDerivAt (fderiv ℝ z) (fderiv ℝ (fderiv ℝ z) v) v :=
      ((hz.fderiv_right (m := 1) (by norm_num)).differentiable (by norm_num) v).hasFDerivAt
    have h3 := ((ContinuousLinearMap.compL ℝ BondVector BondVector ℝ) P).hasFDerivAt.comp v hd2
    have h4 : fderiv ℝ (fun w => P.comp (fderiv ℝ z w)) v = _ := h3.fderiv
    rw [h4]
    refine (ContinuousLinearMap.opNorm_comp_le _ _).trans ?_
    have h5 : ‖(ContinuousLinearMap.compL ℝ BondVector BondVector ℝ) P‖ ≤ 1 := by
      apply ContinuousLinearMap.opNorm_le_bound _ zero_le_one
      intro Q
      simp only [one_mul]
      refine (ContinuousLinearMap.opNorm_comp_le _ _).trans ?_
      have := norm_nonneg Q
      nlinarith
    have := norm_nonneg (fderiv ℝ (fderiv ℝ z) v)
    nlinarith
end YangMills.Construction.ColdStepAtMirrorFrames.ThirdDerivative
end
noncomputable section
open MeasureTheory Set Filter Topology
namespace YangMills.Construction.ColdStepAtMirrorFrames.ThirdDerivative
variable {ι : Type} [Fintype ι] [DecidableEq ι] {X : Type}
variable {ρ : ℝ} {p : ℝ → ℝ} {m κ : ℝ} {Ψ : BondField ι → ℝ} {K : ι → ι → ℝ} {c₁ W a : ℝ}
  {δ : X → X → ℝ} {loc : ι → X}
def secondOrderConst (Dz W : ℝ) : ℝ := Dz ^ 2 * (3 * W ^ 2 + 2 * W)
def remainderConst (Dz W : ℝ) : ℝ := Dz ^ 3 * (10 * W ^ 2 + 21 * W + 1)
def thirdOrderConst (ρ c₁ W co Dz : ℝ) : ℝ :=
  3 * ((W + 2 * byPartsConst ρ c₁ W co) * secondOrderConst Dz W * Dz * W) + remainderConst Dz W * W ^ 2
theorem fieldDerivAlong_fieldC1Bound_scaled {z₁ z₂ : ι → BondVector → BondVector} {Dz : ℝ} {w₁ w₂ : ι → ℝ}
    (h₁ : FieldC2Bound ρ z₁ (fun b => Dz * w₁ b)) (h₂ : FieldC2Bound ρ z₂ (fun b => Dz * w₂ b)) (hρ : 0 < ρ) :
    FieldC1Bound ρ (fieldDerivAlong z₁ z₂) (fun b => (2 * Dz ^ 2) * (w₁ b * w₂ b)) := by
  have := fieldDerivAlong_fieldC1Bound h₁ h₂ hρ
  have e : (fun b => 2 * ((Dz * w₁ b) * (Dz * w₂ b))) = fun b => (2 * Dz ^ 2) * (w₁ b * w₂ b) := by
    funext b
    ring
  rwa [e] at this
theorem bondGradNorm_thirdDerivRemainder_le (h : LocalizedMeasureHyp ρ p m κ Ψ K c₁ W a δ loc) {G : BondField ι → ℝ}
    {E E₃ Dz : ℝ} {Y' c1 c2 c3 : X} (hE : 0 ≤ E) (hEE : E ≤ E₃)
    (hG : ThirdJetBound ρ G E E₃ (fun b => expWeight δ a Y' (loc b)))
    {z₁ z₂ z₃ z₁₂ z₁₃ z₂₃ z₁₂₃ : ι → BondVector → BondVector}
    (F : ThirdFieldBounds ρ δ loc a Dz c1 c2 c3 z₁ z₂ z₃ z₁₂ z₁₃ z₂₃ z₁₂₃) (b : ι)
    (η : BondField ι) (hη : InOpenBalls ρ η) :
    bondGradNorm (thirdDerivRemainder G z₁ z₂ z₃ z₁₂ z₁₃ z₂₃ z₁₂₃) b η ≤
      remainderConst Dz W * E₃ * (expWeight δ (a / 4) Y' c1 * expWeight δ (a / 4) Y' c2 * expWeight δ (a / 4) Y' c3) *
        expWeight δ (a / 4) Y' (loc b) := by
  have hρ := h.measure.pos
  have pl := h.site_dist
  have hκ := h.rate_pos
  have ha0 : 0 ≤ a := by linarith [h.rate_le]
  have Ws := localized_placeWeights h Y'
  have hW : 0 ≤ W := placeWeights_total_nonneg Ws
  have hE₃ : 0 ≤ E₃ := hE.trans hEE
  have hDz := F.one_le
  have hD0 : 0 ≤ Dz := by linarith
  set w₁ := expWeight δ (a / 4) Y' c1 with hw₁
  set w₂ := expWeight δ (a / 4) Y' c2 with hw₂
  set w₃ := expWeight δ (a / 4) Y' c3 with hw₃
  have w₁0 : 0 ≤ w₁ := expWeight_nonneg _ _ _
  have w₂0 : 0 ≤ w₂ := expWeight_nonneg _ _ _
  have w₃0 : 0 ≤ w₃ := expWeight_nonneg _ _ _
  have l1 := F.first.toFieldC1Bound
  have l2 := F.second.toFieldC1Bound
  have l3 := F.third.toFieldC1Bound
  have l12 := fieldDerivAlong_fieldC1Bound_scaled F.first F.second hρ
  have l13 := fieldDerivAlong_fieldC1Bound_scaled F.first F.third hρ
  have A1 : IsAdmissible _ _ _ (Dz * w₁) := isAdmissible_one (loc := loc) pl ha0 Y' c1 hD0
  have A2 : IsAdmissible _ _ _ (Dz * w₂) := isAdmissible_one (loc := loc) pl ha0 Y' c2 hD0
  have A3 : IsAdmissible _ _ _ (Dz * w₃) := isAdmissible_one (loc := loc) pl ha0 Y' c3 hD0
  have B12 : IsAdmissible _ _ _ (Dz * (w₁ * w₂)) := isAdmissible_two (loc := loc) pl ha0 Y' c1 c2 hD0
  have B13 : IsAdmissible _ _ _ (Dz * (w₁ * w₃)) := isAdmissible_two (loc := loc) pl ha0 Y' c1 c3 hD0
  have B23 : IsAdmissible _ _ _ (Dz * (w₂ * w₃)) := isAdmissible_two (loc := loc) pl ha0 Y' c2 c3 hD0
  have C12 : IsAdmissible _ _ _ ((2 * Dz ^ 2) * (w₁ * w₂)) :=
    isAdmissible_two (loc := loc) pl ha0 Y' c1 c2 (by positivity)
  have C13 : IsAdmissible _ _ _ ((2 * Dz ^ 2) * (w₁ * w₃)) :=
    isAdmissible_two (loc := loc) pl ha0 Y' c1 c3 (by positivity)
  have D123 : IsAdmissible _ _ _ (Dz * (w₁ * w₂ * w₃)) := isAdmissible_three (loc := loc) pl ha0 Y' c1 c2 c3 hD0
  have q1 := bondGradNorm_secondDerivAlong_le hG Ws hE hE₃ hρ F.first_second l3 B12 A3 (by positivity) (by positivity) b η hη
  have q2 := bondGradNorm_secondDerivAlong_le hG Ws hE hE₃ hρ l12 l3 C12 A3 (by positivity) (by positivity) b η hη
  have q3 := bondGradNorm_secondDerivAlong_le hG Ws hE hE₃ hρ l2 l13 A2 C13 (by positivity) (by positivity) b η hη
  have q4 := bondGradNorm_secondDerivAlong_le hG Ws hE hE₃ hρ F.first_third l2 B13 A2 (by positivity) (by positivity) b η hη
  have q5 := bondGradNorm_secondDerivAlong_le hG Ws hE hE₃ hρ F.second_third l1 B23 A1 (by positivity) (by positivity) b η hη
  have q6 := bondGradNorm_derivAlong_le hG Ws hE hρ F.all_three D123 (by positivity) b η hη
  have s1 := secondDerivAlong_contDiff hG.smooth F.first_second.smooth l3.smooth
  have s2 := secondDerivAlong_contDiff hG.smooth l12.smooth l3.smooth
  have s3 := secondDerivAlong_contDiff hG.smooth l2.smooth l13.smooth
  have s4 := secondDerivAlong_contDiff hG.smooth F.first_third.smooth l2.smooth
  have s5 := secondDerivAlong_contDiff hG.smooth F.second_third.smooth l1.smooth
  have s6 := derivAlong_contDiff hG.smooth F.all_three.smooth
  have r1 := bondGradNorm_sub_le s1 s2 b η
  have r2 := bondGradNorm_sub_le (s1.sub s2) s3 b η
  have r3 := bondGradNorm_add_le ((s1.sub s2).sub s3) s4 b η
  have r4 := bondGradNorm_add_le (((s1.sub s2).sub s3).add s4) s5 b η
  have r5 := bondGradNorm_add_le ((((s1.sub s2).sub s3).add s4).add s5) s6 b η
  have hq : 0 ≤ expWeight δ (a / 4) Y' (loc b) := expWeight_nonneg _ _ _
  set wq := expWeight δ (a / 4) Y' (loc b) with hwq
  set Om' := w₁ * w₂ * w₃ with hOm
  have base : E₃ * W ^ 2 + 2 * E * W ≤ E₃ * (W ^ 2 + 2 * W) := by
    nlinarith [mul_le_mul_of_nonneg_right hEE hW]
  have hD2 : Dz ^ 2 ≤ Dz ^ 3 := pow_le_pow_right₀ hDz (by norm_num)
  have hD1 : Dz ≤ Dz ^ 3 := by
    have := pow_le_pow_right₀ hDz (by norm_num : 1 ≤ 3)
    simpa using this
  have P0 : 0 ≤ E₃ * (W ^ 2 + 2 * W) * Om' * wq := by positivity
  have b1 : (E₃ * W ^ 2 + 2 * E * W) * (Dz * (w₁ * w₂) * (Dz * w₃)) * wq ≤
      Dz ^ 3 * (E₃ * (W ^ 2 + 2 * W) * Om' * wq) := by
    have e : (E₃ * W ^ 2 + 2 * E * W) * (Dz * (w₁ * w₂) * (Dz * w₃)) * wq =
        (E₃ * W ^ 2 + 2 * E * W) * (Dz ^ 2 * (Om' * wq)) := by
      simp only [hOm]
      ring
    rw [e]
    have c : 0 ≤ Dz ^ 2 * (Om' * wq) := by positivity
    have t1 := mul_le_mul_of_nonneg_right base c
    have t2 := mul_le_mul_of_nonneg_right hD2 P0
    calc _ ≤ _ := t1
      _ = Dz ^ 2 * (E₃ * (W ^ 2 + 2 * W) * Om' * wq) := by ring
      _ ≤ _ := t2
  have b2 : (E₃ * W ^ 2 + 2 * E * W) * ((2 * Dz ^ 2) * (w₁ * w₂) * (Dz * w₃)) * wq ≤
      2 * Dz ^ 3 * (E₃ * (W ^ 2 + 2 * W) * Om' * wq) := by
    have e : (E₃ * W ^ 2 + 2 * E * W) * ((2 * Dz ^ 2) * (w₁ * w₂) * (Dz * w₃)) * wq =
        (E₃ * W ^ 2 + 2 * E * W) * (2 * Dz ^ 3 * (Om' * wq)) := by
      simp only [hOm]
      ring
    rw [e]
    have c : 0 ≤ 2 * Dz ^ 3 * (Om' * wq) := by positivity
    refine (mul_le_mul_of_nonneg_right base c).trans (le_of_eq ?_)
    ring
  have b6 : (E * W + E) * (Dz * Om') * wq ≤ Dz ^ 3 * (E₃ * (W + 1) * Om' * wq) := by
    have c1 : E * W + E ≤ E₃ * (W + 1) := by nlinarith [mul_le_mul_of_nonneg_right hEE hW]
    have c : 0 ≤ Dz * (Om' * wq) := by positivity
    have t1 := mul_le_mul_of_nonneg_right c1 c
    have P1 : 0 ≤ E₃ * (W + 1) * Om' * wq := by positivity
    have t2 := mul_le_mul_of_nonneg_right hD1 P1
    calc _ = (E * W + E) * (Dz * (Om' * wq)) := by ring
      _ ≤ _ := t1
      _ = Dz * (E₃ * (W + 1) * Om' * wq) := by ring
      _ ≤ _ := t2
  have fin : Dz ^ 3 * (E₃ * (W ^ 2 + 2 * W) * Om' * wq) + 2 * Dz ^ 3 * (E₃ * (W ^ 2 + 2 * W) * Om' * wq) +
      2 * Dz ^ 3 * (E₃ * (W ^ 2 + 2 * W) * Om' * wq) + Dz ^ 3 * (E₃ * (W ^ 2 + 2 * W) * Om' * wq) +
      Dz ^ 3 * (E₃ * (W ^ 2 + 2 * W) * Om' * wq) + Dz ^ 3 * (E₃ * (W + 1) * Om' * wq) ≤
      remainderConst Dz W * E₃ * Om' * wq := by
    have e1 : remainderConst Dz W * E₃ * Om' * wq - (Dz ^ 3 * (E₃ * (W ^ 2 + 2 * W) * Om' * wq) +
        2 * Dz ^ 3 * (E₃ * (W ^ 2 + 2 * W) * Om' * wq) +
        2 * Dz ^ 3 * (E₃ * (W ^ 2 + 2 * W) * Om' * wq) + Dz ^ 3 * (E₃ * (W ^ 2 + 2 * W) * Om' * wq) +
        Dz ^ 3 * (E₃ * (W ^ 2 + 2 * W) * Om' * wq) + Dz ^ 3 * (E₃ * (W + 1) * Om' * wq)) =
        Dz ^ 3 * E₃ * Om' * wq * (3 * W ^ 2 + 6 * W) := by
      simp only [remainderConst]
      ring
    have e2 : 0 ≤ Dz ^ 3 * E₃ * Om' * wq * (3 * W ^ 2 + 6 * W) := by positivity
    linarith
  have e0 : bondGradNorm (thirdDerivRemainder G z₁ z₂ z₃ z₁₂ z₁₃ z₂₃ z₁₂₃) b η = bondGradNorm (fun ζ =>
      secondDerivAlong G z₁₂ z₃ ζ - secondDerivAlong G (fieldDerivAlong z₁ z₂) z₃ ζ - secondDerivAlong G z₂ (fieldDerivAlong z₁ z₃) ζ + secondDerivAlong G z₁₃ z₂ ζ +
        secondDerivAlong G z₂₃ z₁ ζ + derivAlong G z₁₂₃ ζ) b η := rfl
  rw [e0]
  linarith
end YangMills.Construction.ColdStepAtMirrorFrames.ThirdDerivative
end
noncomputable section
open MeasureTheory Set Filter Topology
namespace YangMills.Construction.ColdStepAtMirrorFrames.ThirdDerivative
variable {ι : Type} [Fintype ι] [DecidableEq ι] {X : Type}
variable {ρ : ℝ} {p : ℝ → ℝ} {m κ : ℝ} {Ψ : BondField ι → ℝ} {K : ι → ι → ℝ} {c₁ W a : ℝ}
  {δ : X → X → ℝ} {loc : ι → X}
theorem thirdDerivRemainder_contDiff {G : BondField ι → ℝ} {Dz : ℝ} {c1 c2 c3 : X} (hρ : 0 < ρ)
    (hG : ContDiff ℝ 3 G) {z₁ z₂ z₃ z₁₂ z₁₃ z₂₃ z₁₂₃ : ι → BondVector → BondVector}
    (F : ThirdFieldBounds ρ δ loc a Dz c1 c2 c3 z₁ z₂ z₃ z₁₂ z₁₃ z₂₃ z₁₂₃) :
    ContDiff ℝ 1 (thirdDerivRemainder G z₁ z₂ z₃ z₁₂ z₁₃ z₂₃ z₁₂₃) := by
  have l1 := F.first.toFieldC1Bound
  have l2 := F.second.toFieldC1Bound
  have l3 := F.third.toFieldC1Bound
  have l12 := fieldDerivAlong_fieldC1Bound_scaled F.first F.second hρ
  have l13 := fieldDerivAlong_fieldC1Bound_scaled F.first F.third hρ
  have s1 := secondDerivAlong_contDiff hG F.first_second.smooth l3.smooth
  have s2 := secondDerivAlong_contDiff hG l12.smooth l3.smooth
  have s3 := secondDerivAlong_contDiff hG l2.smooth l13.smooth
  have s4 := secondDerivAlong_contDiff hG F.first_third.smooth l2.smooth
  have s5 := secondDerivAlong_contDiff hG F.second_third.smooth l1.smooth
  have s6 := derivAlong_contDiff hG F.all_three.smooth
  exact ((((s1.sub s2).sub s3).add s4).add s5).add s6
theorem abs_ballCovariance_thirdDerivRemainder_le (hCov : BallCovarianceBound)
    (h : LocalizedMeasureHyp ρ p m κ Ψ K c₁ W a δ loc) {g G : BondField ι → ℝ} {E E₃ Dz : ℝ}
    {Y Y' c1 c2 c3 : X} (hE : 0 ≤ E) (hEE : E ≤ E₃)
    (hg : ThirdJetBound ρ g E E₃ (fun b => expWeight δ a Y (loc b)))
    (hG : ThirdJetBound ρ G E E₃ (fun b => expWeight δ a Y' (loc b)))
    {z₁ z₂ z₃ z₁₂ z₁₃ z₂₃ z₁₂₃ : ι → BondVector → BondVector}
    (F : ThirdFieldBounds ρ δ loc a Dz c1 c2 c3 z₁ z₂ z₃ z₁₂ z₁₃ z₂₃ z₁₂₃) :
    |ballCovariance (extendedCutoff ρ p) Ψ g (thirdDerivRemainder G z₁ z₂ z₃ z₁₂ z₁₃ z₂₃ z₁₂₃)| ≤
      m⁻¹ * (E * (remainderConst Dz W * E₃ * (expWeight δ (a / 4) Y' c1 * expWeight δ (a / 4) Y' c2 * expWeight δ (a / 4) Y' c3)) *
        (W * (W * expWeight δ (κ / 4) Y Y'))) := by
  have mc := h.measure
  have hd := mc.data
  have hρ := mc.pos
  have hκ := h.rate_pos
  have pl := h.site_dist
  have ha := h.rate_le
  have hm0 : 0 < m := by linarith [mc.one_le]
  have hg1 : ContDiff ℝ 1 g := hg.smooth.of_le (by norm_num)
  have hR1 := thirdDerivRemainder_contDiff hρ hG.smooth F
  have hW : 0 ≤ W := localized_weight_nonneg h Y
  have hE₃ : 0 ≤ E₃ := hE.trans hEE
  have hDz := F.one_le
  have hCR : 0 ≤ remainderConst Dz W := by
    unfold remainderConst
    positivity
  set Q := remainderConst Dz W * E₃ * (expWeight δ (a / 4) Y' c1 * expWeight δ (a / 4) Y' c2 * expWeight δ (a / 4) Y' c3) with hQ
  have hQ0 : 0 ≤ Q := by
    have := expWeight_nonneg (δ := δ) (a / 4) Y' c1
    have := expWeight_nonneg (δ := δ) (a / 4) Y' c2
    have := expWeight_nonneg (δ := δ) (a / 4) Y' c3
    positivity
  have hA : ∀ b' η, InOpenBalls ρ η → bondGradNorm g b' η ≤ E * expWeight δ a Y (loc b') := by
    intro b' η hη
    apply bondGradNorm_le (mul_nonneg hE (expWeight_nonneg _ _ _))
    intro e'
    exact hg.first η hη b' e'
  have hB : ∀ b', ballL2Norm (extendedCutoff ρ p) Ψ (bondGradNorm (thirdDerivRemainder G z₁ z₂ z₃ z₁₂ z₁₃ z₂₃ z₁₂₃) b') ≤
      Q * expWeight δ (a / 4) Y' (loc b') := fun b' =>
    ballL2Norm_le_const hd (bondGradNorm_continuous hR1 b') (mul_nonneg hQ0 (expWeight_nonneg _ _ _))
      fun η hη => by
        rw [abs_of_nonneg (bondGradNorm_nonneg _ _ _)]
        exact bondGradNorm_thirdDerivRemainder_le h hE hEE hG F b' η hη
  have t := abs_ballCovariance_le_of_sup hCov hρ hm0 hκ.le mc.cutoff mc.dist mc.convex hd hg1 hR1 hA hB
  refine t.trans (mul_le_mul_of_nonneg_left ?_ (inv_nonneg.mpr hm0.le))
  have hW4 := fun z => localized_sum_expWeight_le h (r := κ / 16) le_rfl z
  have pc := sum_sum_expWeight_le pl (κ := κ) (θ₀ := κ / 16) (r₁ := a) (r₂ := a / 4) hκ.le (by linarith)
    (by linarith) (by linarith) hW4 Y Y'
  have e : ∑ b₁, ∑ b₂, E * expWeight δ a Y (loc b₁) * Real.exp (-(κ * δ (loc b₁) (loc b₂))) *
        (Q * expWeight δ (a / 4) Y' (loc b₂)) =
      (E * Q) * ∑ b₁, ∑ b₂, expWeight δ a Y (loc b₁) * expWeight δ κ (loc b₁) (loc b₂) * expWeight δ (a / 4) (loc b₂) Y' := by
    rw [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro b₁ _
    rw [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro b₂ _
    rw [expWeight_symm pl _ Y' (loc b₂)]
    simp only [expWeight]
    ring
  refine (le_of_eq e).trans ?_
  exact mul_le_mul_of_nonneg_left pc (mul_nonneg hE hQ0)
theorem abs_ballCovariance_thirdDerivAlong_le (hCov : BallCovarianceBound)
    (hMom : GaussianMomentBound) (hR : CutoffFactorIsRadialCutoff)
    (h : LocalizedMeasureHyp ρ p m κ Ψ K c₁ W a δ loc) {c co : ℝ} (hc : RimBoundConst ρ p c) (hco : 0 ≤ co)
    (ho : ∀ (b : ι) (ε : ℝ), 0 < ε →
      ballL2Norm (extendedCutoff ρ p) Ψ (fun η => rimBound ρ p c ε ‖η b‖) ≤ co / Real.sqrt m)
    {g G : BondField ι → ℝ} {E E₃ Dz : ℝ} {Y Y' c1 c2 c3 : X} (hE : 0 ≤ E) (hEE : E ≤ E₃)
    (hg : ThirdJetBound ρ g E E₃ (fun b => expWeight δ a Y (loc b)))
    (hG : ThirdJetBound ρ G E E₃ (fun b => expWeight δ a Y' (loc b)))
    {z₁ z₂ z₃ z₁₂ z₁₃ z₂₃ z₁₂₃ : ι → BondVector → BondVector}
    (F : ThirdFieldBounds ρ δ loc a Dz c1 c2 c3 z₁ z₂ z₃ z₁₂ z₁₃ z₂₃ z₁₂₃) :
    |ballCovariance (extendedCutoff ρ p) Ψ g (thirdDerivAlong G z₁ z₂ z₃ z₁₂ z₁₃ z₂₃ z₁₂₃)| ≤
      thirdOrderConst ρ c₁ W co Dz * (E * E₃ / Real.sqrt m) * expWeight δ (κ / 8) Y Y' *
        (expWeight δ (κ / 16) Y' c1 * expWeight δ (κ / 16) Y' c2 * expWeight δ (κ / 16) Y' c3) := by
  have mc := h.measure
  have hd := mc.data
  have hρ := mc.pos
  have hκ := h.rate_pos
  have pl := h.site_dist
  have ha := h.rate_le
  have ha0 : 0 ≤ a := by linarith
  have hm1 := mc.one_le
  have hm0 : 0 < m := by linarith
  have hW : 0 ≤ W := localized_weight_nonneg h Y
  have hE₃ : 0 ≤ E₃ := hE.trans hEE
  have hDz := F.one_le
  have hD0 : 0 ≤ Dz := by linarith
  have Ws := localized_placeWeights h Y'
  have hg1 : ContDiff ℝ 1 g := hg.smooth.of_le (by norm_num)
  have l2 := F.second.toFieldC1Bound
  have l3 := F.third.toFieldC1Bound
  set s := Real.sqrt m with hs
  have hs1 : 1 ≤ s := by
    rw [hs]
    exact Real.one_le_sqrt.mpr hm1
  have hs0 : 0 < s := by linarith
  set w₂ := expWeight δ (a / 4) Y' c2 with hw₂
  set w₃ := expWeight δ (a / 4) Y' c3 with hw₃
  have w₂0 : 0 ≤ w₂ := expWeight_nonneg _ _ _
  have w₃0 : 0 ≤ w₃ := expWeight_nonneg _ _ _
  have A2 : IsAdmissible _ _ _ (Dz * w₂) := isAdmissible_one (loc := loc) pl ha0 Y' c2 hD0
  have A3 : IsAdmissible _ _ _ (Dz * w₃) := isAdmissible_one (loc := loc) pl ha0 Y' c3 hD0
  set H := secondDerivAlong G z₂ z₃ with hHdef
  have hH : ContDiff ℝ 1 H := secondDerivAlong_contDiff hG.smooth l2.smooth l3.smooth
  set Hh := secondOrderConst Dz W * E₃ * (w₂ * w₃) with hHh
  have hCH : 0 ≤ secondOrderConst Dz W := by
    unfold secondOrderConst
    positivity
  have hHh0 : 0 ≤ Hh := by positivity
  have hHd : ∀ b' η, InOpenBalls ρ η → bondGradNorm H b' η ≤ Hh * expWeight δ (a / 4) Y' (loc b') := by
    intro b' η hη
    have q := bondGradNorm_secondDerivAlong_le hG Ws hE hE₃ hρ l2 l3 A2 A3 (by positivity) (by positivity) b' η hη
    refine q.trans ?_
    have w0 := expWeight_nonneg (δ := δ) (a / 4) Y' (loc b')
    apply mul_le_mul_of_nonneg_right _ w0
    have b1 : E₃ * W ^ 2 + 2 * E * W ≤ E₃ * (3 * W ^ 2 + 2 * W) := by
      nlinarith [mul_le_mul_of_nonneg_right hEE hW, mul_nonneg hE₃ (sq_nonneg W)]
    have c0 : 0 ≤ Dz ^ 2 * (w₂ * w₃) := by positivity
    have := mul_le_mul_of_nonneg_right b1 c0
    calc _ = (E₃ * W ^ 2 + 2 * E * W) * (Dz ^ 2 * (w₂ * w₃)) := by ring
      _ ≤ _ := this
      _ = _ := by simp only [hHh, secondOrderConst]; ring
  have hsup : ∀ η, InOpenBalls ρ η → 2 * |H η| ≤ Hh := by
    intro η hη
    have q := abs_secondDerivAlong_le hG Ws hE hρ l2 l3 A2 A3 (by positivity) (by positivity) η hη
    have e1 : 2 * (E * (Dz * w₂ * W) * (Dz * w₃ * W)) ≤ Hh := by
      have b1 : 2 * E * W ^ 2 ≤ E₃ * (3 * W ^ 2 + 2 * W) := by
        nlinarith [mul_le_mul_of_nonneg_right hEE (sq_nonneg W), mul_nonneg hE₃ (sq_nonneg W),
          mul_nonneg hE₃ hW]
      have c0 : 0 ≤ Dz ^ 2 * (w₂ * w₃) := by positivity
      have := mul_le_mul_of_nonneg_right b1 c0
      calc _ = 2 * E * W ^ 2 * (Dz ^ 2 * (w₂ * w₃)) := by ring
        _ ≤ _ := this
        _ = _ := by simp only [hHh, secondOrderConst]; ring
    have : 2 * |H η| ≤ 2 * (E * (Dz * w₂ * W) * (Dz * w₃ * W)) := by linarith
    linarith
  set N : ι → ℝ := fun b => Dz * expWeight δ a (loc b) c1 with hNdef
  have hN0 : ∀ b, 0 ≤ N b := fun b => mul_nonneg hD0 (expWeight_nonneg _ _ _)
  set Cm := W + 2 * byPartsConst ρ c₁ W co with hCm
  have est : ∀ (b : ι) (i : Fin 3),
      |ballCovariance (extendedCutoff ρ p) Ψ g (fun η => (z₁ b (η b)) i * bondPartialDeriv H b η (coordUnit i))| ≤
        Cm * (N b * Hh * E / s) * Real.exp (-(κ / 8 * (δ Y Y' + δ Y' (loc b)))) := by
    intro b i
    have hz := F.first.smooth b
    have hαs : ContDiff ℝ 2 (fun v => (z₁ b v) i) :=
      (EuclideanSpace.proj i : BondVector →L[ℝ] ℝ).contDiff.comp hz
    exact abs_ballCovariance_bondTerm_decay hCov hMom hR h hc hco ho (E₃ := E₃) hE hg hH hHh0 hHd hsup b (norm_coordUnit i)
      (α := fun v => (z₁ b v) i) hαs (hN0 b)
      (fun v hv => (coord_bounds hz i v).1.trans (F.first.norm_le b v hv))
      (fun v hv => (coord_bounds hz i v).2.1.trans (F.first.deriv_le b v hv))
      (fun v hv => (coord_bounds hz i v).2.2.trans (F.first.second_deriv_le b v hv))
  have cf : ∀ (b : ι) (i : Fin 3), Continuous
      (fun η : BondField ι => (z₁ b (η b)) i * bondPartialDeriv H b η (coordUnit i)) := by
    intro b i
    have c1' : Continuous fun η : BondField ι => (z₁ b (η b)) i :=
      (EuclideanSpace.proj i : BondVector →L[ℝ] ℝ).continuous.comp
        ((F.first.smooth b).continuous.comp (continuous_apply b))
    exact c1'.mul (bondPartialDeriv_continuous hH b _)
  have hsplit : thirdDerivAlong G z₁ z₂ z₃ z₁₂ z₁₃ z₂₃ z₁₂₃ = fun η =>
      (∑ b, ∑ i, (z₁ b (η b)) i * bondPartialDeriv H b η (coordUnit i)) +
        thirdDerivRemainder G z₁ z₂ z₃ z₁₂ z₁₃ z₂₃ z₁₂₃ η := by
    funext η
    rw [thirdDerivAlong_split hG.smooth l2.smooth l3.smooth, apply_eq_sum_coordUnit]
    rfl
  have hR1 := thirdDerivRemainder_contDiff hρ hG.smooth F
  have cs1 : ∀ b, Continuous fun η : BondField ι =>
      ∑ i, (z₁ b (η b)) i * bondPartialDeriv H b η (coordUnit i) := fun b =>
    continuous_finsetSum _ fun i _ => cf b i
  have cs2 : Continuous fun η : BondField ι =>
      ∑ b, ∑ i, (z₁ b (η b)) i * bondPartialDeriv H b η (coordUnit i) :=
    continuous_finsetSum _ fun b _ => cs1 b
  rw [hsplit, ballCovariance_add hd hg1.continuous cs2 hR1.continuous,
    ballCovariance_sum hd hg1.continuous (f := fun b η => ∑ i, (z₁ b (η b)) i * bondPartialDeriv H b η (coordUnit i)) cs1]
  have hsum : ∀ b, ballCovariance (extendedCutoff ρ p) Ψ g
      (fun η => ∑ i, (z₁ b (η b)) i * bondPartialDeriv H b η (coordUnit i)) =
      ∑ i, ballCovariance (extendedCutoff ρ p) Ψ g (fun η => (z₁ b (η b)) i * bondPartialDeriv H b η (coordUnit i)) :=
    fun b => ballCovariance_sum hd hg1.continuous (f := fun i η => (z₁ b (η b)) i * bondPartialDeriv H b η (coordUnit i))
      (cf b)
  simp only [hsum]
  have hC3 : 0 ≤ byPartsConst ρ c₁ W co := by
    unfold byPartsConst
    have := mc.c₁_nonneg
    positivity
  set w8 := expWeight δ (κ / 8) Y Y' with hw8
  have hw80 : 0 ≤ w8 := expWeight_nonneg _ _ _
  set v₁ := expWeight δ (κ / 16) Y' c1 with hv₁
  set v₂ := expWeight δ (κ / 16) Y' c2 with hv₂
  set v₃ := expWeight δ (κ / 16) Y' c3 with hv₃
  have v₁0 : 0 ≤ v₁ := expWeight_nonneg _ _ _
  have v₂0 : 0 ≤ v₂ := expWeight_nonneg _ _ _
  have v₃0 : 0 ≤ v₃ := expWeight_nonneg _ _ _
  have S1 : |∑ b, ∑ i, ballCovariance (extendedCutoff ρ p) Ψ g
      (fun η => (z₁ b (η b)) i * bondPartialDeriv H b η (coordUnit i))| ≤
      3 * (Cm * (Dz * Hh * E / s)) * w8 * (W * v₁) := by
    have pb : ∀ b, |∑ i, ballCovariance (extendedCutoff ρ p) Ψ g
        (fun η => (z₁ b (η b)) i * bondPartialDeriv H b η (coordUnit i))| ≤
        3 * (Cm * (Dz * Hh * E / s)) * w8 * (expWeight δ (κ / 8) Y' (loc b) * expWeight δ a (loc b) c1) := by
      intro b
      refine (Finset.abs_sum_le_sum_abs _ _).trans ?_
      refine (Finset.sum_le_sum fun i _ => est b i).trans ?_
      rw [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
      have e : Real.exp (-(κ / 8 * (δ Y Y' + δ Y' (loc b)))) = w8 * expWeight δ (κ / 8) Y' (loc b) := by
        simp only [hw8, expWeight]
        rw [← Real.exp_add]
        congr 1
        ring
      rw [e]
      simp only [hNdef]
      apply le_of_eq
      push_cast
      ring
    refine (Finset.abs_sum_le_sum_abs _ _).trans ?_
    refine (Finset.sum_le_sum fun b _ => pb b).trans ?_
    rw [← Finset.mul_sum]
    apply mul_le_mul_of_nonneg_left _ (by positivity)
    exact sum_expWeight_mul_le pl (by positivity) (by linarith) (by linarith) h.weight_sum Y' c1
  have S2 := abs_ballCovariance_thirdDerivRemainder_le hCov h hE hEE hg hG F (c1 := c1) (c2 := c2) (c3 := c3)
  refine (abs_add_le _ _).trans ?_
  set w₁ := expWeight δ (a / 4) Y' c1 with hw₁
  have hw₁0 : 0 ≤ w₁ := expWeight_nonneg _ _ _
  have le₁ : w₁ ≤ v₁ := expWeight_anti pl (by linarith) _ _
  have le₂ : w₂ ≤ v₂ := expWeight_anti pl (by linarith) _ _
  have le₃ : w₃ ≤ v₃ := expWeight_anti pl (by linarith) _ _
  have le8 : expWeight δ (κ / 4) Y Y' ≤ w8 := expWeight_anti pl (by linarith) _ _
  have hmi : m⁻¹ ≤ 1 / s := by
    have hms : m = s ^ 2 := (Real.sq_sqrt hm0.le).symm
    rw [hms, one_div]
    apply inv_anti₀ hs0
    nlinarith
  have e1 : 3 * (Cm * (Dz * Hh * E / s)) * w8 * (W * v₁) ≤
      3 * (Cm * secondOrderConst Dz W * Dz * W) * (E * E₃ / s) * w8 * (v₁ * v₂ * v₃) := by
    have c0 : 0 ≤ 3 * (Cm * secondOrderConst Dz W * Dz * W) * (E * E₃ / s) * w8 * v₁ := by positivity
    have m23 : w₂ * w₃ ≤ v₂ * v₃ := mul_le_mul le₂ le₃ w₃0 v₂0
    have := mul_le_mul_of_nonneg_left m23 c0
    calc _ = 3 * (Cm * secondOrderConst Dz W * Dz * W) * (E * E₃ / s) * w8 * v₁ * (w₂ * w₃) := by
          simp only [hHh]
          ring
      _ ≤ _ := this
      _ = _ := by ring
  have e2 : m⁻¹ * (E * (remainderConst Dz W * E₃ * (w₁ * w₂ * w₃)) * (W * (W * expWeight δ (κ / 4) Y Y'))) ≤
      remainderConst Dz W * W ^ 2 * (E * E₃ / s) * w8 * (v₁ * v₂ * v₃) := by
    have hCR : 0 ≤ remainderConst Dz W := by
      unfold remainderConst
      positivity
    have c0 : 0 ≤ E * (remainderConst Dz W * E₃ * (w₁ * w₂ * w₃)) * (W * (W * expWeight δ (κ / 4) Y Y')) := by
      have := expWeight_nonneg (δ := δ) (κ / 4) Y Y'
      positivity
    have t1 := mul_le_mul_of_nonneg_right hmi c0
    have m123 : w₁ * w₂ * w₃ ≤ v₁ * v₂ * v₃ :=
      mul_le_mul (mul_le_mul le₁ le₂ w₂0 v₁0) le₃ w₃0 (by positivity)
    have m8 : (w₁ * w₂ * w₃) * expWeight δ (κ / 4) Y Y' ≤ (v₁ * v₂ * v₃) * w8 :=
      mul_le_mul m123 le8 (expWeight_nonneg _ _ _) (by positivity)
    have c1' : 0 ≤ remainderConst Dz W * W ^ 2 * (E * E₃ / s) := by positivity
    have t2 := mul_le_mul_of_nonneg_left m8 c1'
    calc _ ≤ _ := t1
      _ = remainderConst Dz W * W ^ 2 * (E * E₃ / s) * ((w₁ * w₂ * w₃) * expWeight δ (κ / 4) Y Y') := by ring
      _ ≤ _ := t2
      _ = _ := by ring
  have fin : thirdOrderConst ρ c₁ W co Dz * (E * E₃ / s) * w8 * (v₁ * v₂ * v₃) =
      3 * (Cm * secondOrderConst Dz W * Dz * W) * (E * E₃ / s) * w8 * (v₁ * v₂ * v₃) +
        remainderConst Dz W * W ^ 2 * (E * E₃ / s) * w8 * (v₁ * v₂ * v₃) := by
    simp only [thirdOrderConst, hCm]
    ring
  rw [fin]
  exact add_le_add (S1.trans e1) (S2.trans e2)
end YangMills.Construction.ColdStepAtMirrorFrames.ThirdDerivative
namespace YangMills.Construction.ColdStepAtMirrorFrames
open ThirdDerivative in
theorem covarianceThirdDerivBounded_holds (hCov : BallCovarianceBound)
    (hMom : GaussianMomentBound) (hR : CutoffFactorIsRadialCutoff) :
    CovarianceThirdDerivBounded := by
  intro ρ p c₁ W Dz hρ hp hc₁ hW hDz
  obtain ⟨c', hc'⟩ := exists_rimBoundConst hρ hp
  obtain ⟨co, hco, hN⟩ := ballL2Norm_rimBound_le hMom hR hρ hp hc' c₁ W hc₁ hW
  refine ⟨thirdOrderConst ρ c₁ W co Dz, ?_, ?_⟩
  · have hC3 : 0 ≤ byPartsConst ρ c₁ W co := by
      unfold byPartsConst
      positivity
    unfold thirdOrderConst secondOrderConst remainderConst
    positivity
  · intro ι X _ _ m κ a Ψ K δ loc g G E E₃ Y Y' c1 c2 c3 z₁ z₂ z₃ z₁₂ z₁₃ z₂₃ z₁₂₃ h hE hEE hg hG hF
    exact abs_ballCovariance_thirdDerivAlong_le hCov hMom hR h hc' hco (hN ι m κ _ Ψ K h.measure) hE hEE hg hG hF
end YangMills.Construction.ColdStepAtMirrorFrames
end
