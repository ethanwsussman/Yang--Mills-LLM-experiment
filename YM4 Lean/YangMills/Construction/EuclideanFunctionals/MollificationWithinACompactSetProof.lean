import YangMills.Construction.EuclideanFunctionals.MollificationWithinACompactSet
import YangMills.Construction.EuclideanFunctionals.SharpNormOnFunctionsOfClassC1Proof
import Mathlib
set_option autoImplicit false
open Filter Topology MeasureTheory
open scoped Convolution ContDiff
noncomputable section
namespace YangMills.Construction.EuclideanFunctionals.Mollification
theorem norm_le_euclidNormVec (v : R4) : ‖v‖ ≤ TorusMetric.euclidNormVec v := by apply _root_.YangMills.Construction.EuclideanFunctionals.Moments.norm_le_euclidNormVec <;> assumption
theorem euclidNormVec_le_two_mul_norm (v : R4) : TorusMetric.euclidNormVec v ≤ 2 * ‖v‖ := by apply _root_.YangMills.Construction.EuclideanFunctionals.Moments.euclidNormVec_le_two_mul_norm <;> assumption
abbrev ambientMetric : R4 → R4 → ℝ :=
  ReflectionPositivity.AxisMirror.Ambient.metric defaultMirrorData
    ReflectionPositivity.AxisMirror.Ambient.euclidean
theorem closureWrt_subset_closure (Z : Set R4) :
    MetricNotions.closureWrt ambientMetric Z ⊆ closure Z := by apply _root_.YangMills.Construction.EuclideanFunctionals.SharpNormC1.closureWrt_subset_closure <;> assumption
theorem closure_subset_closureWrt (Z : Set R4) :
    closure Z ⊆ MetricNotions.closureWrt ambientMetric Z := by apply _root_.YangMills.Construction.EuclideanFunctionals.SharpNormC1.closure_subset_closureWrt <;> assumption
theorem contDiff_and_hasCompactSupport {f : R4 → ℂ} (hf : f ∈ C1c ℂ) :
    ContDiff ℝ 1 f ∧ HasCompactSupport f := by apply _root_.YangMills.Construction.EuclideanFunctionals.SharpNormC1.contDiff_hasCompactSupport_of_mem <;> assumption
def smoothed (φ : ContDiffBump (0 : R4)) (g : R4 → ℂ) : R4 → ℂ :=
  φ.normed volume ⋆[ContinuousLinearMap.lsmul ℝ ℝ, volume] g
def shrinkingBump (δ : ℝ) (hδ : 0 < δ) (j : ℕ) : ContDiffBump (0 : R4) where
  rIn := δ / (j + 1) / 2
  rOut := δ / (j + 1)
  rIn_pos := by positivity
  rIn_lt_rOut := half_lt_self (by positivity)
theorem tendsto_shrinkingBump_rOut (δ : ℝ) (hδ : 0 < δ) :
    Tendsto (fun j => (shrinkingBump δ hδ j).rOut) atTop (𝓝 0) :=
  tendsto_const_div_atTop_nhds_zero_nat δ |>.comp (tendsto_add_atTop_nat 1) |>.congr fun j => by
    simp [shrinkingBump]
theorem contDiff_smoothed (φ : ContDiffBump (0 : R4)) {g : R4 → ℂ} (hg : Continuous g) :
    ContDiff ℝ ∞ (smoothed φ g) :=
  (φ.hasCompactSupport_normed (μ := volume)).contDiff_convolution_left _
    φ.contDiff_normed hg.locallyIntegrable
theorem hasCompactSupport_smoothed (φ : ContDiffBump (0 : R4)) {g : R4 → ℂ}
    (hk : HasCompactSupport g) : HasCompactSupport (smoothed φ g) :=
  (φ.hasCompactSupport_normed (μ := volume)).convolution _ hk
theorem tsupport_smoothed_subset (φ : ContDiffBump (0 : R4)) {g : R4 → ℂ} {δ : ℝ}
    (hr : φ.rOut ≤ δ) : tsupport (smoothed φ g) ⊆ Metric.cthickening δ (tsupport g) := by
  refine closure_minimal (fun x hx => ?_) Metric.isClosed_cthickening
  obtain ⟨a, ha, b, hb, rfl⟩ := Set.mem_add.1 (support_convolution_subset _ hx)
  rw [φ.support_normed_eq] at ha
  refine Metric.mem_cthickening_of_dist_le _ b _ _ (subset_tsupport _ hb) ?_
  have : ‖a‖ < φ.rOut := by simpa using ha
  rw [dist_eq_norm, add_sub_cancel_right]
  exact this.le.trans hr
theorem l1Norm_smoothed_le (φ : ContDiffBump (0 : R4)) {g : R4 → ℂ}
    (hc : Continuous g) (hk : HasCompactSupport g) :
    l1Norm (smoothed φ g) ≤ l1Norm g := by
  have hρ : Integrable (φ.normed volume) volume := φ.integrable_normed
  have hn : Integrable (fun y => ‖g y‖) volume := (hc.integrable_of_hasCompactSupport hk).norm
  have hle : ∀ x, ‖smoothed φ g x‖ ≤
      (φ.normed volume ⋆[ContinuousLinearMap.lsmul ℝ ℝ, volume] fun y => ‖g y‖) x := by
    intro x
    simp only [smoothed, convolution_def]
    refine (norm_integral_le_integral_norm _).trans (le_of_eq ?_)
    refine integral_congr_ae (Eventually.of_forall fun t => ?_)
    simp [abs_of_nonneg (φ.nonneg_normed t)]
  have hint := integral_convolution (ContinuousLinearMap.lsmul ℝ ℝ) hρ hn
  have hone : ∫ x, φ.normed volume x = 1 := φ.integral_normed
  rw [hone] at hint
  simp only [ContinuousLinearMap.lsmul_apply, one_smul] at hint
  unfold l1Norm
  rw [← hint]
  exact integral_mono_of_nonneg (Eventually.of_forall fun x => norm_nonneg _)
    (hρ.integrable_convolution _ hn) (Eventually.of_forall hle)
theorem fderiv_smoothed (φ : ContDiffBump (0 : R4)) {g : R4 → ℂ} (hg : ContDiff ℝ 1 g)
    (hk : HasCompactSupport g) (v x : R4) :
    fderiv ℝ (smoothed φ g) x v = smoothed φ (fun y => fderiv ℝ g y v) x := by
  have hl : LocallyIntegrable (φ.normed volume) volume := φ.integrable_normed.locallyIntegrable
  have hd := hk.hasFDerivAt_convolution_right (ContinuousLinearMap.lsmul ℝ ℝ) hl hg x
  rw [smoothed, hd.fderiv]
  exact convolution_precompR_apply _ hl (hk.fderiv ℝ) (hg.continuous_fderiv one_ne_zero) x v
theorem tendstoUniformly_smoothed {g : R4 → ℂ} (hc : Continuous g) (hk : HasCompactSupport g)
    (φ : ℕ → ContDiffBump (0 : R4)) (hφ : Tendsto (fun j => (φ j).rOut) atTop (𝓝 0)) :
    TendstoUniformly (fun j => smoothed (φ j) g) g atTop := by
  have hu : UniformContinuous g := hk.uniformContinuous_of_continuous hc
  rw [Metric.tendstoUniformly_iff]
  intro ε hε
  obtain ⟨d, hd, hud⟩ := Metric.uniformContinuous_iff.1 hu (ε / 2) (half_pos hε)
  filter_upwards [hφ.eventually (gt_mem_nhds hd)] with j hj x
  have hb := (φ j).dist_normed_convolution_le (μ := volume) (x₀ := x) hc.aestronglyMeasurable
    (ε := ε / 2) fun y hy => (hud (hy.trans hj)).le
  rw [dist_comm]
  exact hb.trans_lt (half_lt_self hε)
theorem isRealValued_smoothed (φ : ContDiffBump (0 : R4)) {g : R4 → ℂ}
    (hr : IsRealValued g) : IsRealValued (smoothed φ g) := by
  intro x
  have he : smoothed φ g x = ((∫ t, φ.normed volume t * (g (x - t)).re : ℝ) : ℂ) := by
    rw [← integral_complex_ofReal]
    simp only [smoothed, convolution_def]
    refine integral_congr_ae (Eventually.of_forall fun t => ?_)
    apply Complex.ext <;> simp [hr (x - t)]
  rw [he, Complex.ofReal_im]
theorem mollificationInCompact_holds : MollificationInCompact := by
  intro O hO h hh hsub
  obtain ⟨hC, hk⟩ := contDiff_and_hasCompactSupport hh
  have hts : tsupport h ⊆ O := (closure_subset_closureWrt _).trans hsub
  obtain ⟨δ, hδ, hδO⟩ := hk.isCompact.exists_cthickening_subset_open hO hts
  have hcont : Continuous h := hC.continuous
  have hr : ∀ j : ℕ, (shrinkingBump δ hδ j).rOut ≤ δ := fun j => by
    have h1 : (1 : ℝ) ≤ j + 1 := by
      have : (0 : ℝ) ≤ j := Nat.cast_nonneg j
      linarith
    exact div_le_self hδ.le h1
  refine ⟨Metric.cthickening δ (tsupport h), hk.isCompact.cthickening, hδO,
    (closureWrt_subset_closure _).trans (Metric.self_subset_cthickening _),
    fun j => smoothed (shrinkingBump δ hδ j) h, fun j _ => ⟨⟨?_, ?_⟩, ?_, ?_⟩, ⟨?_, fun i => ?_⟩,
    fun hreal j _ => isRealValued_smoothed _ hreal⟩
  · exact contDiff_smoothed _ hcont
  · exact hasCompactSupport_smoothed _ hk
  · exact (closureWrt_subset_closure _).trans (tsupport_smoothed_subset _ (hr j))
  · exact l1Norm_smoothed_le _ hcont hk
  · exact tendstoUniformly_smoothed hcont hk _ (tendsto_shrinkingBump_rOut δ hδ)
  · have hkd : HasCompactSupport fun y => fderiv ℝ h y (Pi.single i 1) :=
      (hk.fderiv ℝ).comp_left (g := fun L : R4 →L[ℝ] ℂ => L (Pi.single i 1)) (by simp)
    have hcd : Continuous fun y => fderiv ℝ h y (Pi.single i 1) :=
      (hC.continuous_fderiv one_ne_zero).clm_apply continuous_const
    have := tendstoUniformly_smoothed hcd hkd _ (tendsto_shrinkingBump_rOut δ hδ)
    simpa only [fderiv_smoothed _ hC hk] using this
end YangMills.Construction.EuclideanFunctionals.Mollification
