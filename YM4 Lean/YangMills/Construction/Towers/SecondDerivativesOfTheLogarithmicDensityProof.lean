import YangMills.Construction.Towers.SecondDerivativesOfTheLogarithmicDensity
import YangMills.Construction.Towers.VariationsOfALocalFamily
import Mathlib
set_option autoImplicit false
open MeasureTheory Set Filter Topology
open ContinuousLinearMap (mulLeftRight compL)
noncomputable section
set_option linter.unusedSectionVars false
namespace YangMills.Construction
namespace BanachResolvent
variable {A : Type*} [NormedRing A] [NormedAlgebra ℝ A] [CompleteSpace A]
def resolventAt (M : A) (w : ℝ) : A := Ring.inverse (M + w • (1 : A))
def logIntegrand (τ : A →L[ℝ] ℂ) (M : A) (w : ℝ) : ℂ :=
  τ (((1 + w)⁻¹ : ℝ) • (1 : A) - resolventAt M w)
def traceGrad (τ : A →L[ℝ] ℂ) (R : A) : A →L[ℝ] ℂ := compL ℝ A A ℂ τ (mulLeftRight ℝ A R R)
def traceHess (τ : A →L[ℝ] ℂ) (R : A) : A →L[ℝ] A →L[ℝ] ℂ :=
  (compL ℝ A (A →L[ℝ] A) (A →L[ℝ] ℂ) (compL ℝ A A ℂ τ))
    ((mulLeftRight ℝ A).precompR A R (-(mulLeftRight ℝ A R R)) +
      (mulLeftRight ℝ A).precompL A (-(mulLeftRight ℝ A R R)) R)
theorem traceGrad_apply (τ : A →L[ℝ] ℂ) (R H : A) : traceGrad τ R H = τ (R * H * R) := by
  simp [traceGrad]
theorem traceHess_apply (τ : A →L[ℝ] ℂ) (R H K : A) :
    traceHess τ R H K = -τ (R * K * (R * H * R)) - τ (R * H * R * K * R) := by
  simp [traceHess, ContinuousLinearMap.precompR, ContinuousLinearMap.precompL, sub_eq_add_neg]
theorem continuous_traceGrad (τ : A →L[ℝ] ℂ) : Continuous (traceGrad τ) := by
  unfold traceGrad
  fun_prop
theorem continuous_traceHess (τ : A →L[ℝ] ℂ) : Continuous (traceHess τ) := by
  unfold traceHess
  fun_prop
theorem norm_traceGrad_le (τ : A →L[ℝ] ℂ) (R : A) : ‖traceGrad τ R‖ ≤ ‖τ‖ * ‖R‖ ^ 2 := by
  refine ContinuousLinearMap.opNorm_le_bound _ (by positivity) fun H => ?_
  rw [traceGrad_apply]
  calc ‖τ (R * H * R)‖ ≤ ‖τ‖ * ‖R * H * R‖ := τ.le_opNorm _
    _ ≤ ‖τ‖ * (‖R‖ * ‖H‖ * ‖R‖) := by
        gcongr
        exact (norm_mul_le _ _).trans (by gcongr; exact norm_mul_le _ _)
    _ = ‖τ‖ * ‖R‖ ^ 2 * ‖H‖ := by ring
theorem norm_traceHess_le (τ : A →L[ℝ] ℂ) (R : A) : ‖traceHess τ R‖ ≤ 2 * ‖τ‖ * ‖R‖ ^ 3 := by
  refine ContinuousLinearMap.opNorm_le_bound₂ _ (by positivity) fun H K => ?_
  rw [traceHess_apply]
  have h1 : ‖R * K * (R * H * R)‖ ≤ ‖R‖ ^ 3 * ‖H‖ * ‖K‖ := by
    calc ‖R * K * (R * H * R)‖ ≤ ‖R * K‖ * ‖R * H * R‖ := norm_mul_le _ _
      _ ≤ (‖R‖ * ‖K‖) * ((‖R‖ * ‖H‖) * ‖R‖) := by
          gcongr
          · exact norm_mul_le _ _
          · exact (norm_mul_le _ _).trans (by gcongr; exact norm_mul_le _ _)
      _ = ‖R‖ ^ 3 * ‖H‖ * ‖K‖ := by ring
  have h2 : ‖R * H * R * K * R‖ ≤ ‖R‖ ^ 3 * ‖H‖ * ‖K‖ := by
    calc ‖R * H * R * K * R‖ ≤ (((‖R‖ * ‖H‖) * ‖R‖) * ‖K‖) * ‖R‖ := by
          refine (norm_mul_le _ _).trans ?_
          gcongr
          refine (norm_mul_le _ _).trans ?_
          gcongr
          refine (norm_mul_le _ _).trans ?_
          gcongr
          exact norm_mul_le _ _
      _ = ‖R‖ ^ 3 * ‖H‖ * ‖K‖ := by ring
  calc ‖-τ (R * K * (R * H * R)) - τ (R * H * R * K * R)‖
      ≤ ‖τ (R * K * (R * H * R))‖ + ‖τ (R * H * R * K * R)‖ := by
        simpa using norm_sub_le (-τ (R * K * (R * H * R))) (τ (R * H * R * K * R))
    _ ≤ ‖τ‖ * ‖R * K * (R * H * R)‖ + ‖τ‖ * ‖R * H * R * K * R‖ :=
        add_le_add (τ.le_opNorm _) (τ.le_opNorm _)
    _ ≤ ‖τ‖ * (‖R‖ ^ 3 * ‖H‖ * ‖K‖) + ‖τ‖ * (‖R‖ ^ 3 * ‖H‖ * ‖K‖) := by gcongr
    _ = 2 * ‖τ‖ * ‖R‖ ^ 3 * ‖H‖ * ‖K‖ := by ring
theorem hasFDerivAt_resolventAt {M : A} {w : ℝ} (h : IsUnit (M + w • (1 : A))) :
    HasFDerivAt (fun N : A => resolventAt N w)
      (-mulLeftRight ℝ A (resolventAt M w) (resolventAt M w)) M := by
  obtain ⟨u, hu⟩ := h
  have h1 := hasFDerivAt_ringInverse (𝕜 := ℝ) u
  have hinv : ((u⁻¹ : Aˣ) : A) = resolventAt M w := by
    rw [resolventAt, ← hu, Ring.inverse_unit]
  rw [hinv, hu] at h1
  have h2 : HasFDerivAt (fun N : A => N + w • (1 : A)) (ContinuousLinearMap.id ℝ A) M :=
    (hasFDerivAt_id M).add_const _
  have h3 := HasFDerivAt.comp M h1 h2
  simpa [resolventAt, Function.comp_def] using h3
theorem hasFDerivAt_logIntegrand (τ : A →L[ℝ] ℂ) {M : A} {w : ℝ} (h : IsUnit (M + w • (1 : A))) :
    HasFDerivAt (fun N : A => logIntegrand τ N w) (traceGrad τ (resolventAt M w)) M := by
  have h1 := ((hasFDerivAt_resolventAt h).const_sub (((1 + w)⁻¹ : ℝ) • (1 : A)))
  have h2 := τ.hasFDerivAt.comp M h1
  have h3 : τ.comp (-(-mulLeftRight ℝ A (resolventAt M w) (resolventAt M w))) =
      traceGrad τ (resolventAt M w) := by
    ext H
    simp [traceGrad]
  rw [h3] at h2
  simpa [logIntegrand, Function.comp_def] using h2
theorem hasFDerivAt_traceGrad_resolventAt (τ : A →L[ℝ] ℂ) {M : A} {w : ℝ}
    (h : IsUnit (M + w • (1 : A))) :
    HasFDerivAt (fun N : A => traceGrad τ (resolventAt N w)) (traceHess τ (resolventAt M w)) M := by
  have hR := hasFDerivAt_resolventAt h
  have h1 := (mulLeftRight ℝ A).hasFDerivAt_of_bilinear hR hR
  exact ((compL ℝ A A ℂ τ).hasFDerivAt).comp M h1
structure ResolventControl (U : Set A) (K a N : ℝ) : Prop where
  isOpen : IsOpen U
  unit : ∀ M ∈ U, ∀ w : ℝ, 0 ≤ w → IsUnit (M + w • (1 : A))
  bound : ∀ M ∈ U, ∀ w : ℝ, 0 ≤ w → ‖resolventAt M w‖ ≤ K * (a + w)⁻¹
  norm : ∀ M ∈ U, ‖M‖ ≤ N
  a_pos : 0 < a
  a_le : a ≤ 1
  K_nonneg : 0 ≤ K
theorem continuousOn_resolventAt {M : A} (h : ∀ w : ℝ, 0 ≤ w → IsUnit (M + w • (1 : A))) :
    ContinuousOn (resolventAt M) (Ici 0) := by
  intro w hw
  obtain ⟨u, hu⟩ := h w hw
  have h1 : ContinuousAt Ring.inverse (M + w • (1 : A)) := by
    rw [← hu]
    exact NormedRing.inverse_continuousAt u
  have h2 : ContinuousAt (fun v : ℝ => M + v • (1 : A)) w := by fun_prop
  exact (ContinuousAt.comp (f := fun v : ℝ => M + v • (1 : A)) h1 h2).continuousWithinAt
def decayWeight (a w : ℝ) : ℝ := (w + a) ^ (-2 : ℝ)
theorem decayWeight_eq {a w : ℝ} (h : 0 < a + w) : decayWeight a w = ((a + w)⁻¹) ^ 2 := by
  rw [decayWeight, add_comm w a, Real.rpow_neg h.le, Real.rpow_two, inv_pow]
theorem integrable_decayWeight {a : ℝ} (ha : 0 < a) :
    Integrable (decayWeight a) (volume.restrict (Ioi 0)) := by
  have := integrableOn_add_rpow_Ioi_of_lt (a := -2) (c := 0) (m := a) (by norm_num) (by linarith)
  exact this
theorem integrable_of_decayWeight_bound {E : Type*} [NormedAddCommGroup E] {f : ℝ → E} {a c : ℝ}
    (ha : 0 < a) (hf : ContinuousOn f (Ici 0))
    (hb : ∀ w : ℝ, 0 < w → ‖f w‖ ≤ c * decayWeight a w) :
    Integrable f (volume.restrict (Ioi 0)) := by
  refine Integrable.mono' ((integrable_decayWeight ha).const_mul c)
    ((hf.mono Ioi_subset_Ici_self).aestronglyMeasurable measurableSet_Ioi) ?_
  exact (ae_restrict_iff' measurableSet_Ioi).2 (ae_of_all _ fun w hw => hb w hw)
section Domain
variable {U : Set A} {K a N : ℝ} (hU : ResolventControl U K a N) (τ : A →L[ℝ] ℂ)
include hU
theorem norm_resolventAt_sq_le {M : A} (hM : M ∈ U) {w : ℝ} (hw : 0 ≤ w) :
    ‖resolventAt M w‖ ^ 2 ≤ K ^ 2 * decayWeight a w := by
  have ha := hU.a_pos
  have h0 : 0 < a + w := by linarith
  rw [decayWeight_eq h0, ← mul_pow]
  exact pow_le_pow_left₀ (norm_nonneg _) (hU.bound M hM w hw) 2
theorem norm_resolventAt_cube_le {M : A} (hM : M ∈ U) {w : ℝ} (hw : 0 ≤ w) :
    ‖resolventAt M w‖ ^ 3 ≤ K ^ 3 * a⁻¹ * decayWeight a w := by
  have ha := hU.a_pos
  have hK := hU.K_nonneg
  have h0 : 0 < a + w := by linarith
  have h1 : (a + w)⁻¹ ≤ a⁻¹ := inv_anti₀ ha (by linarith)
  rw [decayWeight_eq h0]
  calc ‖resolventAt M w‖ ^ 3 ≤ (K * (a + w)⁻¹) ^ 3 :=
        pow_le_pow_left₀ (norm_nonneg _) (hU.bound M hM w hw) 3
    _ = K ^ 3 * (a + w)⁻¹ * ((a + w)⁻¹) ^ 2 := by ring
    _ ≤ K ^ 3 * a⁻¹ * ((a + w)⁻¹) ^ 2 := by gcongr
theorem logIntegrand_arg_eq {M : A} {w : ℝ} (hw : 0 ≤ w) (hM : M ∈ U) :
    ((1 + w)⁻¹ : ℝ) • (1 : A) - resolventAt M w =
      ((1 + w)⁻¹ : ℝ) • (resolventAt M w * (M - 1)) := by
  have hR : resolventAt M w * (M + w • (1 : A)) = 1 :=
    Ring.inverse_mul_cancel _ (hU.unit M hM w hw)
  have h1 : M - 1 = (M + w • (1 : A)) - (1 + w) • (1 : A) := by
    rw [add_smul, one_smul]; abel
  have h2 : (1 + w) ≠ 0 := by positivity
  rw [h1, mul_sub, hR, mul_smul_comm, mul_one, smul_sub, smul_smul, inv_mul_cancel₀ h2, one_smul]
theorem norm_logIntegrand_le {M : A} (hM : M ∈ U) {w : ℝ} (hw : 0 ≤ w) :
    ‖logIntegrand τ M w‖ ≤ ‖τ‖ * (K * (N + ‖(1 : A)‖)) * decayWeight a w := by
  have ha := hU.a_pos
  have hK := hU.K_nonneg
  have h0 : 0 < a + w := by linarith
  have h1 : (1 + w)⁻¹ ≤ (a + w)⁻¹ := inv_anti₀ h0 (by linarith [hU.a_le])
  have h2 : ‖M - 1‖ ≤ N + ‖(1 : A)‖ := (norm_sub_le _ _).trans (by linarith [hU.norm M hM])
  have h3 : 0 ≤ (1 + w)⁻¹ := by positivity
  rw [logIntegrand, logIntegrand_arg_eq hU hw hM, decayWeight_eq h0]
  calc ‖τ (((1 + w)⁻¹ : ℝ) • (resolventAt M w * (M - 1)))‖
      ≤ ‖τ‖ * ‖((1 + w)⁻¹ : ℝ) • (resolventAt M w * (M - 1))‖ := τ.le_opNorm _
    _ ≤ ‖τ‖ * ((1 + w)⁻¹ * (‖resolventAt M w‖ * ‖M - 1‖)) := by
        rw [norm_smul, Real.norm_of_nonneg h3]
        gcongr
        exact norm_mul_le _ _
    _ ≤ ‖τ‖ * ((a + w)⁻¹ * ((K * (a + w)⁻¹) * (N + ‖(1 : A)‖))) := by
        have := hU.bound M hM w hw
        gcongr
    _ = ‖τ‖ * (K * (N + ‖(1 : A)‖)) * ((a + w)⁻¹) ^ 2 := by ring
theorem continuousOn_logIntegrand {M : A} (hM : M ∈ U) :
    ContinuousOn (logIntegrand τ M) (Ici 0) := by
  have h1 := continuousOn_resolventAt (hU.unit M hM)
  have h2 : ContinuousOn (fun w : ℝ => (1 + w)⁻¹) (Ici 0) := by
    refine ContinuousOn.inv₀ (by fun_prop) fun w hw => ?_
    have : (0 : ℝ) ≤ w := hw
    positivity
  have h3 : ContinuousOn (fun w : ℝ => ((1 + w)⁻¹ : ℝ) • (1 : A) - resolventAt M w) (Ici 0) :=
    (h2.smul continuousOn_const).sub h1
  exact τ.continuous.comp_continuousOn h3
theorem integrable_logIntegrand {M : A} (hM : M ∈ U) :
    Integrable (logIntegrand τ M) (volume.restrict (Ioi 0)) :=
  integrable_of_decayWeight_bound hU.a_pos (continuousOn_logIntegrand hU τ hM)
    fun _ hw => norm_logIntegrand_le hU τ hM hw.le
theorem norm_traceGrad_resolventAt_le {M : A} (hM : M ∈ U) {w : ℝ} (hw : 0 ≤ w) :
    ‖traceGrad τ (resolventAt M w)‖ ≤ ‖τ‖ * K ^ 2 * decayWeight a w :=
  (norm_traceGrad_le τ _).trans (by
    have := norm_resolventAt_sq_le hU hM hw
    calc ‖τ‖ * ‖resolventAt M w‖ ^ 2 ≤ ‖τ‖ * (K ^ 2 * decayWeight a w) := by gcongr
      _ = _ := by ring)
theorem norm_traceHess_resolventAt_le {M : A} (hM : M ∈ U) {w : ℝ} (hw : 0 ≤ w) :
    ‖traceHess τ (resolventAt M w)‖ ≤ 2 * ‖τ‖ * (K ^ 3 * a⁻¹) * decayWeight a w :=
  (norm_traceHess_le τ _).trans (by
    have := norm_resolventAt_cube_le hU hM hw
    calc 2 * ‖τ‖ * ‖resolventAt M w‖ ^ 3 ≤ 2 * ‖τ‖ * (K ^ 3 * a⁻¹ * decayWeight a w) := by gcongr
      _ = _ := by ring)
theorem continuousOn_traceGrad_resolventAt {M : A} (hM : M ∈ U) :
    ContinuousOn (fun w => traceGrad τ (resolventAt M w)) (Ici 0) :=
  (continuous_traceGrad τ).comp_continuousOn (continuousOn_resolventAt (hU.unit M hM))
theorem continuousOn_traceHess_resolventAt {M : A} (hM : M ∈ U) :
    ContinuousOn (fun w => traceHess τ (resolventAt M w)) (Ici 0) :=
  (continuous_traceHess τ).comp_continuousOn (continuousOn_resolventAt (hU.unit M hM))
theorem integrable_traceGrad {M : A} (hM : M ∈ U) :
    Integrable (fun w => traceGrad τ (resolventAt M w)) (volume.restrict (Ioi 0)) :=
  integrable_of_decayWeight_bound hU.a_pos (continuousOn_traceGrad_resolventAt hU τ hM)
    fun _ hw => norm_traceGrad_resolventAt_le hU τ hM hw.le
theorem aestronglyMeasurable_traceHess {M : A} (hM : M ∈ U) :
    AEStronglyMeasurable (fun w => traceHess τ (resolventAt M w)) (volume.restrict (Ioi 0)) :=
  (integrable_of_decayWeight_bound (E := A →L[ℝ] A →L[ℝ] ℂ) hU.a_pos
    (continuousOn_traceHess_resolventAt hU τ hM)
    fun _ hw => norm_traceHess_resolventAt_le hU τ hM hw.le).aestronglyMeasurable
theorem integrable_traceHess_apply {M : A} (hM : M ∈ U) (H K : A) :
    Integrable (fun w => traceHess τ (resolventAt M w) H K) (volume.restrict (Ioi 0)) :=
  ((integrable_of_decayWeight_bound (E := A →L[ℝ] A →L[ℝ] ℂ) hU.a_pos
    (continuousOn_traceHess_resolventAt hU τ hM)
    fun _ hw => norm_traceHess_resolventAt_le hU τ hM hw.le).apply_continuousLinearMap
      H).apply_continuousLinearMap K
theorem integrable_traceGrad_apply {M : A} (hM : M ∈ U) (H : A) :
    Integrable (fun w => traceGrad τ (resolventAt M w) H) (volume.restrict (Ioi 0)) :=
  (integrable_traceGrad hU τ hM).apply_continuousLinearMap H
theorem integral_traceHess_apply {M : A} (hM : M ∈ U) (H K : A) :
    (∫ w in Ioi (0 : ℝ), traceHess τ (resolventAt M w)) H K =
      ∫ w in Ioi (0 : ℝ), traceHess τ (resolventAt M w) H K := by
  have h := integrable_of_decayWeight_bound (E := A →L[ℝ] A →L[ℝ] ℂ) hU.a_pos
    (continuousOn_traceHess_resolventAt hU τ hM)
    fun _ hw => norm_traceHess_resolventAt_le hU τ hM hw.le
  rw [ContinuousLinearMap.integral_apply h H,
    ContinuousLinearMap.integral_apply (h.apply_continuousLinearMap H) K]
theorem integral_traceGrad_apply {M : A} (hM : M ∈ U) (H : A) :
    (∫ w in Ioi (0 : ℝ), traceGrad τ (resolventAt M w)) H =
      ∫ w in Ioi (0 : ℝ), traceGrad τ (resolventAt M w) H :=
  ContinuousLinearMap.integral_apply (integrable_traceGrad hU τ hM) H
theorem hasFDerivAt_integral_logIntegrand {M : A} (hM : M ∈ U) :
    HasFDerivAt (fun N' : A => ∫ w in Ioi (0 : ℝ), logIntegrand τ N' w)
      (∫ w in Ioi (0 : ℝ), traceGrad τ (resolventAt M w)) M := by
  refine hasFDerivAt_integral_of_dominated_of_fderiv_le (𝕜 := ℝ)
    (F' := fun M w => traceGrad τ (resolventAt M w))
    (bound := fun w => ‖τ‖ * K ^ 2 * decayWeight a w) (hU.isOpen.mem_nhds hM) ?_
    (integrable_logIntegrand hU τ hM) (integrable_traceGrad hU τ hM).aestronglyMeasurable ?_
    ((integrable_decayWeight hU.a_pos).const_mul _) ?_
  · filter_upwards [hU.isOpen.mem_nhds hM] with x hx
    exact (integrable_logIntegrand hU τ hx).aestronglyMeasurable
  · exact (ae_restrict_iff' measurableSet_Ioi).2
      (ae_of_all _ fun w hw x hx => norm_traceGrad_resolventAt_le hU τ hx (le_of_lt hw))
  · exact (ae_restrict_iff' measurableSet_Ioi).2
      (ae_of_all _ fun w hw x hx => hasFDerivAt_logIntegrand τ (hU.unit x hx w (le_of_lt hw)))
theorem hasFDerivAt_integral_traceGrad {M : A} (hM : M ∈ U) :
    HasFDerivAt (fun N' : A => ∫ w in Ioi (0 : ℝ), traceGrad τ (resolventAt N' w))
      (∫ w in Ioi (0 : ℝ), traceHess τ (resolventAt M w)) M := by
  refine hasFDerivAt_integral_of_dominated_of_fderiv_le (𝕜 := ℝ)
    (F' := fun M w => traceHess τ (resolventAt M w))
    (bound := fun w => 2 * ‖τ‖ * (K ^ 3 * a⁻¹) * decayWeight a w) (hU.isOpen.mem_nhds hM) ?_
    (integrable_traceGrad hU τ hM) (aestronglyMeasurable_traceHess hU τ hM) ?_
    ((integrable_decayWeight hU.a_pos).const_mul _) ?_
  · filter_upwards [hU.isOpen.mem_nhds hM] with x hx
    exact (integrable_traceGrad hU τ hx).aestronglyMeasurable
  · exact (ae_restrict_iff' measurableSet_Ioi).2
      (ae_of_all _ fun w hw x hx => norm_traceHess_resolventAt_le hU τ hx (le_of_lt hw))
  · exact (ae_restrict_iff' measurableSet_Ioi).2
      (ae_of_all _ fun w hw x hx =>
        hasFDerivAt_traceGrad_resolventAt τ (hU.unit x hx w (le_of_lt hw)))
theorem continuousOn_integral_traceHess :
    ContinuousOn (fun M : A => ∫ w in Ioi (0 : ℝ), traceHess τ (resolventAt M w)) U := by
  refine continuousOn_of_dominated
    (bound := fun w => 2 * ‖τ‖ * (K ^ 3 * a⁻¹) * decayWeight a w) ?_ ?_
    ((integrable_decayWeight hU.a_pos).const_mul _) ?_
  · exact fun x hx => (aestronglyMeasurable_traceHess hU τ hx)
  · exact fun x hx => (ae_restrict_iff' measurableSet_Ioi).2
      (ae_of_all _ fun w hw => norm_traceHess_resolventAt_le hU τ hx (le_of_lt hw))
  · refine (ae_restrict_iff' measurableSet_Ioi).2 (ae_of_all _ fun w hw => ?_)
    intro x hx
    have h1 := (hasFDerivAt_resolventAt (hU.unit x hx w (le_of_lt hw))).continuousAt
    exact ((continuous_traceHess τ).continuousAt.comp h1).continuousWithinAt
theorem contDiffOn_integral_logIntegrand :
    ContDiffOn ℝ 2 (fun M : A => ∫ w in Ioi (0 : ℝ), logIntegrand τ M w) U := by
  have e1 : ∀ M ∈ U, fderiv ℝ (fun N' : A => ∫ w in Ioi (0 : ℝ), logIntegrand τ N' w) M =
      ∫ w in Ioi (0 : ℝ), traceGrad τ (resolventAt M w) :=
    fun M hM => (hasFDerivAt_integral_logIntegrand hU τ hM).fderiv
  have e2 : ∀ M ∈ U, fderiv ℝ (fun N' : A => ∫ w in Ioi (0 : ℝ), traceGrad τ (resolventAt N' w)) M =
      ∫ w in Ioi (0 : ℝ), traceHess τ (resolventAt M w) :=
    fun M hM => (hasFDerivAt_integral_traceGrad hU τ hM).fderiv
  have h1 : ContDiffOn ℝ 1 (fun M : A => ∫ w in Ioi (0 : ℝ), traceGrad τ (resolventAt M w)) U := by
    rw [show (1 : WithTop ℕ∞) = 0 + 1 by norm_num, contDiffOn_succ_iff_fderiv_of_isOpen hU.isOpen]
    refine ⟨fun M hM =>
      (hasFDerivAt_integral_traceGrad hU τ hM).differentiableAt.differentiableWithinAt,
      by simp, ?_⟩
    rw [contDiffOn_zero]
    exact (continuousOn_integral_traceHess hU τ).congr e2
  rw [show (2 : WithTop ℕ∞) = 1 + 1 by norm_num, contDiffOn_succ_iff_fderiv_of_isOpen hU.isOpen]
  exact ⟨fun M hM =>
    (hasFDerivAt_integral_logIntegrand hU τ hM).differentiableAt.differentiableWithinAt,
    by simp, h1.congr e1⟩
theorem deriv_deriv_integral_logIntegrand {Q : ℝ × ℝ → A} (c : A) (hQ : ContDiff ℝ 2 Q)
    (h0 : Q 0 + c ∈ U) {g : ℝ × ℝ → ℂ}
    (hg : ∀ᶠ p in 𝓝 (0 : ℝ × ℝ), g p = ∫ w in Ioi (0 : ℝ), logIntegrand τ (Q p + c) w) :
    deriv (fun s : ℝ => deriv (fun t : ℝ => g (s, t)) 0) 0 =
      (∫ w in Ioi (0 : ℝ), traceHess τ (resolventAt (Q 0 + c) w))
        (deriv (fun s : ℝ => Q (s, 0)) 0) (deriv (fun t : ℝ => Q (0, t)) 0) +
      (∫ w in Ioi (0 : ℝ), traceGrad τ (resolventAt (Q 0 + c) w))
        (deriv (fun s : ℝ => deriv (fun t : ℝ => Q (s, t)) 0) 0) := by
  have hU0 : ∀ᶠ p in 𝓝 (0 : ℝ × ℝ), Q p + c ∈ U :=
    (hQ.continuous.add continuous_const).continuousAt.eventually_mem (hU.isOpen.mem_nhds h0)
  have hW2 := eventually_eventually_nhds.2 (hg.and hU0)
  have hline : Tendsto (fun s : ℝ => (s, (0 : ℝ))) (𝓝 0) (𝓝 (0 : ℝ × ℝ)) := by
    have h : Continuous (fun s : ℝ => (s, (0 : ℝ))) := by fun_prop
    exact h.tendsto 0
  have hS := hline.eventually hW2
  have hQd : ∀ p, HasFDerivAt Q (fderiv ℝ Q p) p :=
    fun p => (hQ.differentiable (by norm_num) p).hasFDerivAt
  have ht : ∀ s : ℝ, HasDerivAt (fun t : ℝ => Q (s, t)) (fderiv ℝ Q (s, 0) (0, 1)) 0 := by
    intro s
    have h1 : HasDerivAt (fun t : ℝ => (s, t)) ((0 : ℝ), (1 : ℝ)) 0 :=
      (hasDerivAt_const 0 s).prodMk (hasDerivAt_id 0)
    exact (hQd (s, 0)).comp_hasDerivAt 0 h1
  have hs : HasDerivAt (fun s : ℝ => Q (s, 0)) (fderiv ℝ Q (0, 0) (1, 0)) 0 := by
    have h1 : HasDerivAt (fun s : ℝ => (s, (0 : ℝ))) ((1 : ℝ), (0 : ℝ)) 0 :=
      (hasDerivAt_id 0).prodMk (hasDerivAt_const 0 0)
    have hq : HasFDerivAt Q (fderiv ℝ Q (0, 0)) ((fun s : ℝ => (s, (0 : ℝ))) 0) := hQd (0, 0)
    exact HasFDerivAt.comp_hasDerivAt (f := fun s : ℝ => (s, (0 : ℝ))) 0 hq h1
  have inner : (fun s : ℝ => deriv (fun t : ℝ => g (s, t)) 0) =ᶠ[𝓝 0]
      fun s : ℝ => (∫ w in Ioi (0 : ℝ), traceGrad τ (resolventAt (Q (s, 0) + c) w))
        (fderiv ℝ Q (s, 0) (0, 1)) := by
    filter_upwards [hS] with s hs'
    have hmem : Q (s, 0) + c ∈ U := hs'.self_of_nhds.2
    have e : (fun t : ℝ => g (s, t)) =ᶠ[𝓝 0]
        fun t : ℝ => ∫ w in Ioi (0 : ℝ), logIntegrand τ (Q (s, t) + c) w := by
      have tl : Tendsto (fun t : ℝ => (s, t)) (𝓝 0) (𝓝 (s, 0)) := by
        have h : Continuous (fun t : ℝ => (s, t)) := by fun_prop
        exact h.tendsto 0
      exact (tl.eventually hs').mono fun t ht' => ht'.1
    rw [e.deriv_eq]
    exact ((hasFDerivAt_integral_logIntegrand hU τ hmem).comp_hasDerivAt (0 : ℝ)
      ((ht s).add_const c)).deriv
  have hd : Differentiable ℝ (fderiv ℝ Q) :=
    (hQ.fderiv_right (m := 1) (by norm_num)).differentiable (by norm_num)
  have a1 : HasDerivAt (fun s : ℝ => ∫ w in Ioi (0 : ℝ), traceGrad τ (resolventAt (Q (s, 0) + c) w))
      ((∫ w in Ioi (0 : ℝ), traceHess τ (resolventAt (Q 0 + c) w)) (fderiv ℝ Q (0, 0) (1, 0))) 0 := by
    have hq : HasFDerivAt (fun N' : A => ∫ w in Ioi (0 : ℝ), traceGrad τ (resolventAt N' w))
        (∫ w in Ioi (0 : ℝ), traceHess τ (resolventAt (Q 0 + c) w))
        ((fun s : ℝ => Q (s, 0) + c) 0) :=
      hasFDerivAt_integral_traceGrad hU τ h0
    exact hq.comp_hasDerivAt (0 : ℝ) (hs.add_const c)
  have a2 : DifferentiableAt ℝ (fun s : ℝ => fderiv ℝ Q (s, 0) (0, 1)) 0 := by
    have h1 : DifferentiableAt ℝ (fun s : ℝ => (s, (0 : ℝ))) 0 := by fun_prop
    have hq : DifferentiableAt ℝ (fderiv ℝ Q) ((fun s : ℝ => (s, (0 : ℝ))) 0) := hd (0, 0)
    exact (DifferentiableAt.comp (f := fun s : ℝ => (s, (0 : ℝ))) (0 : ℝ) hq h1).clm_apply
      (differentiableAt_const _)
  have a3 := a1.clm_apply a2.hasDerivAt
  have e1 : deriv (fun s : ℝ => Q (s, 0)) 0 = fderiv ℝ Q (0, 0) (1, 0) := hs.deriv
  have e2 : deriv (fun t : ℝ => Q (0, t)) 0 = fderiv ℝ Q (0, 0) (0, 1) := (ht 0).deriv
  have e3 : (fun s : ℝ => deriv (fun t : ℝ => Q (s, t)) 0) =
      fun s : ℝ => fderiv ℝ Q (s, 0) (0, 1) := funext fun s => (ht s).deriv
  rw [inner.deriv_eq, a3.deriv, e1, e2, e3]
  rfl
end Domain
theorem resolventControl_ball {M₀ : A} {c a : ℝ} (hc : 0 < c) (ha : 0 < a) (hac : a ≤ c)
    (ha1 : a ≤ 1) (hu : ∀ w : ℝ, 0 ≤ w → IsUnit (M₀ + w • (1 : A)))
    (hb : ∀ w : ℝ, 0 ≤ w → ‖resolventAt M₀ w‖ ≤ (c + w)⁻¹) :
    ResolventControl (Metric.ball M₀ (c / 2)) 2 a (‖M₀‖ + c / 2) := by
  have key : ∀ M ∈ Metric.ball M₀ (c / 2), ∀ w : ℝ, 0 ≤ w →
      IsUnit (M + w • (1 : A)) ∧ ‖resolventAt M w‖ ≤ 2 * (a + w)⁻¹ := by
    intro M hM w hw
    have he : ‖M - M₀‖ < c / 2 := by simpa [dist_eq_norm] using hM
    set R := resolventAt M₀ w with hR
    set X := M₀ + w • (1 : A) with hX
    have hRX : R * X = 1 := Ring.inverse_mul_cancel _ (hu w hw)
    have hXR : X * R = 1 := Ring.mul_inverse_cancel _ (hu w hw)
    have hRn : ‖R‖ ≤ (c + w)⁻¹ := hb w hw
    have hcw : 0 < c + w := by linarith
    have hsmall : ‖R * (M - M₀)‖ ≤ 1 / 2 := by
      calc ‖R * (M - M₀)‖ ≤ ‖R‖ * ‖M - M₀‖ := norm_mul_le _ _
        _ ≤ (c + w)⁻¹ * (c / 2) := by gcongr
        _ ≤ 1 / 2 := by
            rw [inv_mul_le_iff₀ hcw]
            linarith
    have hsum : M + w • (1 : A) = X * (1 + R * (M - M₀)) := by
      rw [mul_add, mul_one, ← mul_assoc, hXR, one_mul, hX]
      abel
    have hu2 : IsUnit (1 + R * (M - M₀)) := by
      have hlt : ‖-(R * (M - M₀))‖ < 1 := by
        rw [norm_neg]
        linarith
      have := (Units.oneSub (-(R * (M - M₀))) hlt).isUnit
      simpa using this
    have hunit : IsUnit (M + w • (1 : A)) := by
      rw [hsum]
      exact (hu w hw).mul hu2
    refine ⟨hunit, ?_⟩
    set Y := resolventAt M w with hY
    have hXY : (M + w • (1 : A)) * Y = 1 := Ring.mul_inverse_cancel _ hunit
    have hYeq : Y = R - R * (M - M₀) * Y := by
      have h1 : R * ((M + w • (1 : A)) * Y) = R := by rw [hXY, mul_one]
      have h2 : M + w • (1 : A) = X + (M - M₀) := by rw [hX]; abel
      rw [h2, add_mul, mul_add, ← mul_assoc, hRX, one_mul, ← mul_assoc] at h1
      rw [eq_sub_iff_add_eq]
      exact h1
    have hYn : ‖Y‖ ≤ ‖R‖ + 1 / 2 * ‖Y‖ := by
      calc ‖Y‖ = ‖R - R * (M - M₀) * Y‖ := by rw [← hYeq]
        _ ≤ ‖R‖ + ‖R * (M - M₀) * Y‖ := norm_sub_le _ _
        _ ≤ ‖R‖ + ‖R * (M - M₀)‖ * ‖Y‖ := by gcongr; exact norm_mul_le _ _
        _ ≤ ‖R‖ + 1 / 2 * ‖Y‖ := by gcongr
    have haw : (c + w)⁻¹ ≤ (a + w)⁻¹ := inv_anti₀ (by linarith) (by linarith)
    linarith
  refine ⟨Metric.isOpen_ball, fun M hM w hw => (key M hM w hw).1,
    fun M hM w hw => (key M hM w hw).2, fun M hM => ?_, ha, ha1, by norm_num⟩
  have he : ‖M - M₀‖ < c / 2 := by simpa [dist_eq_norm] using hM
  have := norm_le_insert' M M₀
  linarith
end BanachResolvent
namespace Tower.LocalFamilies
open OperatorCalculus OneLoopNotation AbelianFieldDensity BanachResolvent
section Operators
variable {H : Type} [NormedAddCommGroup H] [InnerProductSpace ℂ H]
theorem scalarOp_ofReal (r : ℝ) :
    (scalarOp (r : ℂ) : BddOp H) = r • (1 : BddOp H) := by
  ext f
  simp [scalarOp]
theorem addScalar_eq_add_smul (S : BddOp H) (w : ℝ) :
    addScalar S w = S + w • (1 : BddOp H) := by
  rw [addScalar, scalarOp_ofReal]
theorem inverseOp_eq_ringInverse {X : BddOp H} (h : IsTwoSidedInverse X (inverseOp X)) :
    IsUnit X ∧ inverseOp X = Ring.inverse X := by
  let u : (BddOp H)ˣ := ⟨X, inverseOp X, h.1, h.2⟩
  refine ⟨u.isUnit, ?_⟩
  have h1 : Ring.inverse (u : BddOp H) = ((u⁻¹ : (BddOp H)ˣ) : BddOp H) :=
    Ring.inverse_unit u
  exact h1.symm
theorem exists_clm_of_boundedLinearTrace (f : BddOp H → ℂ) (k : ℕ) (h : IsBoundedLinearTrace f k) :
    ∃ L : BddOp H →L[ℝ] ℂ, ∀ S, L S = f S := by
  have hzero : f 0 = 0 := by
    have := h.2.1 0
    simpa using this
  have hadd : ∀ S S', f (S + S') = f S + f S' := fun S S' => by
    have := h.1 S S' 1
    simpa using this
  have hsmul : ∀ (r : ℝ) S, f (r • S) = (r : ℂ) * f S := fun r S => by
    have := h.1 0 S (r : ℂ)
    simpa [hzero] using this
  let L₀ : BddOp H →ₗ[ℝ] ℂ :=
    { toFun := f
      map_add' := hadd
      map_smul' := fun r S => by simp [hsmul] }
  exact ⟨L₀.mkContinuous k fun S => h.2.1 S, fun S => rfl⟩
end Operators
variable {J B : Type}
theorem abs_twoBondField_le (b b' : B) (s t : ℝ) (c : B) :
    |twoBondField b b' s t c| ≤ |s| + |t| := by
  classical
  have h1 : |s * bondIndicator b c| ≤ |s| := by
    unfold bondIndicator
    split_ifs <;> simp
  have h2 : |t * bondIndicator b' c| ≤ |t| := by
    unfold bondIndicator
    split_ifs <;> simp
  exact (abs_add_le _ _).trans (add_le_add h1 h2)
theorem twoBondField_zero_zero (b b' : B) : twoBondField b b' 0 0 = fun _ => 0 := by
  funext c
  simp [twoBondField]
theorem twoBondField_left (b b' : B) (s : ℝ) :
    twoBondField b b' s 0 = fun c => s * bondIndicator b c := by
  funext c
  simp [twoBondField]
theorem twoBondField_right (b b' : B) (t : ℝ) :
    twoBondField b b' 0 t = fun c => t * bondIndicator b' c := by
  funext c
  simp [twoBondField]
theorem logTraceAt_secondDerivative_facts {position : J → InfiniteLattice.AmbientSpace}
    {tail : B → InfiniteLattice.AmbientSpace}
    {m m' : ℕ} {z C : ℝ} {T : (B → ℝ) → BddOp (IndexL2 J)} (hz : 0 < z)
    (hset : IsLocalExpansionSetting position tail m m' z C T) (b b' : B)
    (hQ : ContDiff ℝ 2 (fun p : ℝ × ℝ => T (twoBondField b b' p.1 p.2))) (n : Fin 4 → ℤ) :
    ContDiffAt ℝ 2 (fun p : ℝ × ℝ => logTraceAt position T z (twoBondField b b' p.1 p.2)
        (PeriodicOperators.castVec n)) 0 ∧
      MeasureTheory.IntegrableOn (fun w : ℝ => traceAt position (secondOrderResolvent T z b b' w)
        (PeriodicOperators.castVec n)) (Set.Ioi 0) ∧
      logTraceHessian position T z (PeriodicOperators.castVec n) b b' =
        ∫ w in Set.Ioi (0 : ℝ), traceAt position (secondOrderResolvent T z b b' w)
          (PeriodicOperators.castVec n) := by
  obtain ⟨L, hL⟩ := exists_clm_of_boundedLinearTrace _ _ (hset.space.trace_bounded n)
  obtain ⟨r, hr, hsm⟩ := hset.lower_bound
  have hshift : ∀ θ : B → ℝ, (∀ c, |θ c| ≤ r) →
      SectorDecomposition.ShiftedHalfPositive z (T θ) :=
    fun θ h => ⟨hset.family.selfAdjoint θ, hsm θ h⟩
  have hinv : ∀ θ : B → ℝ, (∀ c, |θ c| ≤ r) → ∀ w : ℝ, 0 ≤ w →
      IsUnit (addScalar (T θ) z + w • (1 : BddOp (IndexL2 J))) ∧
      inverseOp (addScalar (addScalar (T θ) z) w) = resolventAt (addScalar (T θ) z) w ∧
      ‖resolventAt (addScalar (T θ) z) w‖ ≤ (z / 2 + w)⁻¹ := by
    intro θ h w hw
    obtain ⟨h1, h2⟩ := (hset.space.logShifted (T θ) (hshift θ h)).1 w hw
    obtain ⟨hu, he⟩ := inverseOp_eq_ringInverse h1
    have e := addScalar_eq_add_smul (addScalar (T θ) z) w
    have e2 : inverseOp (addScalar (addScalar (T θ) z) w) = resolventAt (addScalar (T θ) z) w := by
      rw [he, e, resolventAt]
    refine ⟨e ▸ hu, e2, ?_⟩
    rw [← e2]
    exact h2
  have h0small : ∀ c : B, |(fun _ : B => (0 : ℝ)) c| ≤ r := fun c => by simpa using hr.le
  set M₀ := addScalar (T fun _ => 0) z with hM₀
  have hapos : 0 < min (z / 2) 1 := lt_min (by positivity) one_pos
  have hU := resolventControl_ball (M₀ := M₀) (c := z / 2) (a := min (z / 2) 1) (by positivity)
    hapos (min_le_left _ _) (min_le_right _ _) (fun w hw => (hinv _ h0small w hw).1)
    (fun w hw => (hinv _ h0small w hw).2.2)
  set U := Metric.ball M₀ (z / 2 / 2) with hUdef
  have hM₀U : M₀ ∈ U := Metric.mem_ball_self (by positivity)
  set x := PeriodicOperators.castVec n with hx
  have hrep : ∀ θ : B → ℝ, (∀ c, |θ c| ≤ r) → addScalar (T θ) z ∈ U →
      logTraceAt position T z θ x =
        ∫ w in Set.Ioi (0 : ℝ), logIntegrand L (addScalar (T θ) z) w := by
    intro θ h hmem
    obtain ⟨_, _, h3, h4, _, _, _⟩ := hset.space.logShifted (T θ) (hshift θ h)
    have hI := hset.space.log_eq_integral (T θ) (hshift θ h)
    have h4' : ∃ l : ℝ, Tendsto (fun y : ℝ => ∫ w in (0 : ℝ)..y,
        ‖resolventDiff (addScalar (T θ) z) w‖) atTop (nhds l) := by
      obtain ⟨l, hl⟩ := h4
      exact ⟨l, by simpa only [abs_norm] using hl⟩
    obtain ⟨_, _, _, _, ht, he⟩ := hset.space.trace_integral n _ h3 h4'
    have hpt : ∀ w ∈ Set.Ioi (0 : ℝ), traceAt position
        (resolventDiff (addScalar (T θ) z) w) x = logIntegrand L (addScalar (T θ) z) w := by
      intro w hw
      have hw0 : (0 : ℝ) ≤ w := le_of_lt hw
      rw [← hL]
      unfold logIntegrand resolventDiff
      rw [scalarOp_ofReal, (hinv θ h w hw0).2.1]
    have hInt : MeasureTheory.IntegrableOn (fun w : ℝ => traceAt position
        (resolventDiff (addScalar (T θ) z) w) x) (Set.Ioi 0) :=
      (integrable_logIntegrand hU L hmem).congr
        ((ae_restrict_iff' measurableSet_Ioi).2 (ae_of_all _ fun w hw => (hpt w hw).symm))
    have ht2 := intervalIntegral_tendsto_integral_Ioi 0 hInt tendsto_id
    unfold logTraceAt
    rw [hI]
    refine he.trans ?_
    rw [tendsto_nhds_unique ht ht2]
    exact setIntegral_congr_fun measurableSet_Ioi hpt
  set c : BddOp (IndexL2 J) := z • (1 : BddOp (IndexL2 J)) with hc
  set Q : ℝ × ℝ → BddOp (IndexL2 J) := fun p => T (twoBondField b b' p.1 p.2) with hQdef
  have hQc : ∀ p, Q p + c = addScalar (Q p) z := fun p => (addScalar_eq_add_smul _ _).symm
  have hQ0 : Q 0 + c = M₀ := by
    rw [hQc, hM₀]
    simp only [hQdef, Prod.fst_zero, Prod.snd_zero, twoBondField_zero_zero]
  have hcont : Continuous fun p : ℝ × ℝ => Q p + c := hQ.continuous.add continuous_const
  have hnear : ∀ᶠ p in 𝓝 (0 : ℝ × ℝ), Q p + c ∈ U :=
    hcont.continuousAt.eventually_mem (hU.isOpen.mem_nhds (hQ0 ▸ hM₀U))
  have hsmall : ∀ᶠ p in 𝓝 (0 : ℝ × ℝ), |p.1| + |p.2| < r := by
    have h1 : Continuous fun p : ℝ × ℝ => |p.1| + |p.2| := by fun_prop
    have h2 : (fun p : ℝ × ℝ => |p.1| + |p.2|) 0 < r := by simpa using hr
    exact h1.continuousAt.eventually (gt_mem_nhds h2)
  have hg : ∀ᶠ p in 𝓝 (0 : ℝ × ℝ), logTraceAt position T z (twoBondField b b' p.1 p.2) x =
      ∫ w in Set.Ioi (0 : ℝ), logIntegrand L (Q p + c) w := by
    filter_upwards [hnear, hsmall] with p hp1 hp2
    have h1 : addScalar (T (twoBondField b b' p.1 p.2)) z ∈ U := by
      have := hQc p
      rw [this] at hp1
      exact hp1
    rw [hrep _ (fun e => (abs_twoBondField_le b b' p.1 p.2 e).trans hp2.le) h1, hQc]
  have hmix := deriv_deriv_integral_logIntegrand hU L c hQ (hQ0 ▸ hM₀U) hg
  have e1 : deriv (fun s : ℝ => Q (s, 0)) 0 = firstVar T b := by
    unfold firstVar
    congr 1
    funext s
    simp only [hQdef, twoBondField_left]
  have e2 : deriv (fun t : ℝ => Q (0, t)) 0 = firstVar T b' := by
    unfold firstVar
    congr 1
    funext t
    simp only [hQdef, twoBondField_right]
  have e3 : deriv (fun s : ℝ => deriv (fun t : ℝ => Q (s, t)) 0) 0 = secondVar T b b' := rfl
  erw [e1, e2, e3] at hmix
  rw [hQ0] at hmix
  have hfree : ∀ w : ℝ, 0 ≤ w → baseResolvent T z w = resolventAt M₀ w :=
    fun w hw => (hinv _ h0small w hw).2.1
  have hpt : ∀ w ∈ Set.Ioi (0 : ℝ),
      traceHess L (resolventAt M₀ w) (firstVar T b) (firstVar T b') +
        traceGrad L (resolventAt M₀ w) (secondVar T b b') =
      traceAt position (secondOrderResolvent T z b b' w) x := by
    intro w hw
    have hw0 : (0 : ℝ) ≤ w := le_of_lt hw
    rw [← hL, secondOrderResolvent, hfree w hw0, traceHess_apply, traceGrad_apply]
    simp only [← ContinuousLinearMap.mul_def, map_sub, mul_assoc]
    ring
  have hi1 := integrable_traceHess_apply hU L hM₀U (firstVar T b) (firstVar T b')
  have hi2 := integrable_traceGrad_apply hU L hM₀U (secondVar T b b')
  refine ⟨?_, ?_, ?_⟩
  · have h1 : ContDiffAt ℝ 2 (fun M : BddOp (IndexL2 J) =>
        ∫ w in Set.Ioi (0 : ℝ), logIntegrand L M w) (Q 0 + c) :=
      (contDiffOn_integral_logIntegrand hU L).contDiffAt (hU.isOpen.mem_nhds (hQ0 ▸ hM₀U))
    have h2 : ContDiffAt ℝ 2 (fun p : ℝ × ℝ => Q p + c) 0 :=
      (hQ.add contDiff_const).contDiffAt
    have h3 : ContDiffAt ℝ 2
        (fun p : ℝ × ℝ => ∫ w in Set.Ioi (0 : ℝ), logIntegrand L (Q p + c) w) 0 :=
      ContDiffAt.comp (g := fun M : BddOp (IndexL2 J) =>
        ∫ w in Set.Ioi (0 : ℝ), logIntegrand L M w) (f := fun p : ℝ × ℝ => Q p + c)
        (0 : ℝ × ℝ) h1 h2
    exact h3.congr_of_eventuallyEq hg
  · exact (hi1.add hi2).congr
      ((ae_restrict_iff' measurableSet_Ioi).2 (ae_of_all _ fun w hw => hpt w hw))
  · have h1 : logTraceHessian position T z x b b' = deriv (fun s : ℝ => deriv (fun t : ℝ =>
        logTraceAt position T z (twoBondField b b' (s, t).1 (s, t).2) x) 0) 0 := rfl
    rw [h1, hmix, integral_traceHess_apply hU L hM₀U, integral_traceGrad_apply hU L hM₀U,
      ← integral_add hi1 hi2]
    exact setIntegral_congr_fun measurableSet_Ioi hpt
theorem logTraceSecondDerivative_integralFormula (hv : LocalFamilyVariations) :
    LogTraceSecondDerivative.IntegralFormula := by
  intro J B position tail m m' z C T hz hC hset n b b'
  exact logTraceAt_secondDerivative_facts hz hset b b'
    (hv J B position tail m m' z C T hz hC hset b b').1 n
end Tower.LocalFamilies
end YangMills.Construction
end
