import YangMills.Construction.SpectralTheory.SpectralPushforwardLemmas
import YangMills.Construction.SpectralTheory.StrongConvergenceOfBoundedIntegrals
import YangMills.Construction.SpectralTheory.UnboundedFunctionalCalculusStatement
import Mathlib
set_option autoImplicit false
open MeasureTheory Set Filter Topology
open scoped ENNReal InnerProductSpace ComplexConjugate
noncomputable section
namespace YangMills.Construction.BorelCalculus.Unbounded
open YangMills.Construction.BorelSpectral YangMills.Construction.BorelCalculus
open YangMills.Construction.HilbertSpaceBasics (UnboundedOp IsAdjointOf IsSelfAdjointOp)
variable {n : ℕ} {Y : Set (Fin n → ℝ)} {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H]
  [CompleteSpace H] {E : SpectralMeasure Y H} {g h k : Y → ℂ} {ψ φ : H}
theorem truncate_apply_of_norm_le {r : ℕ} {y : Y} (hy : ‖g y‖ ≤ r) : truncate g r y = g y :=
  indicator_of_mem (show y ∈ {y | ‖g y‖ ≤ (r : ℝ)} from hy) g
theorem truncate_apply_of_not_norm_le {r : ℕ} {y : Y} (hy : ¬‖g y‖ ≤ r) : truncate g r y = 0 :=
  indicator_of_notMem (show y ∉ {y | ‖g y‖ ≤ (r : ℝ)} from hy) g
theorem norm_truncate_apply_le_norm (g : Y → ℂ) (r : ℕ) (y : Y) : ‖truncate g r y‖ ≤ ‖g y‖ := by
  by_cases hy : ‖g y‖ ≤ (r : ℝ)
  · rw [truncate_apply_of_norm_le hy]
  · rw [truncate_apply_of_not_norm_le hy, norm_zero]
    exact norm_nonneg _
theorem norm_truncate_apply_le (g : Y → ℂ) (r : ℕ) (y : Y) : ‖truncate g r y‖ ≤ r := by
  by_cases hy : ‖g y‖ ≤ (r : ℝ)
  · rwa [truncate_apply_of_norm_le hy]
  · rw [truncate_apply_of_not_norm_le hy, norm_zero]
    positivity
theorem measurable_truncate (hg : Measurable g) (r : ℕ) : Measurable (truncate g r) :=
  hg.indicator (measurableSet_le hg.norm measurable_const)
theorem isBoundedFn_truncate (g : Y → ℂ) (r : ℕ) : IsBoundedFn (truncate g r) := by apply _root_.YangMills.Construction.SpectralPushforward.isBoundedFn_truncate <;> assumption
theorem tendsto_truncate_apply (g : Y → ℂ) (y : Y) :
    Tendsto (fun r => truncate g r y) atTop (𝓝 (g y)) := by
  refine tendsto_const_nhds.congr' ?_
  obtain ⟨r₀, hr₀⟩ := exists_nat_ge ‖g y‖
  filter_upwards [eventually_ge_atTop r₀] with r hr
  exact (truncate_apply_of_norm_le (hr₀.trans (by exact_mod_cast hr))).symm
theorem truncate_apply_congr {g g' : Y → ℂ} {y : Y} (h : g y = g' y) (r : ℕ) :
    truncate g r y = truncate g' r y := by
  by_cases hy : ‖g y‖ ≤ (r : ℝ)
  · rw [truncate_apply_of_norm_le hy, truncate_apply_of_norm_le (h ▸ hy), h]
  · rw [truncate_apply_of_not_norm_le hy, truncate_apply_of_not_norm_le (h ▸ hy)]
theorem truncate_conjFn (g : Y → ℂ) (r : ℕ) :
    truncate (conjFn g) r = conjFn (truncate g r) := by
  funext y
  by_cases hy : ‖g y‖ ≤ (r : ℝ)
  · have hy' : ‖conjFn g y‖ ≤ (r : ℝ) := by simpa [conjFn] using hy
    rw [truncate_apply_of_norm_le hy']
    simp [conjFn, truncate_apply_of_norm_le hy]
  · have hy' : ¬‖conjFn g y‖ ≤ (r : ℝ) := by simpa [conjFn] using hy
    rw [truncate_apply_of_not_norm_le hy']
    simp [conjFn, truncate_apply_of_not_norm_le hy]
theorem norm_truncate_sub_truncate_sq_le (g : Y → ℂ) {r s : ℕ} (hrs : r ≤ s) (y : Y) :
    ‖truncate g r y - truncate g s y‖ ^ 2 ≤ ‖truncate g r y - g y‖ ^ 2 := by
  by_cases h₁ : ‖g y‖ ≤ (r : ℝ)
  · have h₂ : ‖g y‖ ≤ (s : ℝ) := h₁.trans (by exact_mod_cast hrs)
    rw [truncate_apply_of_norm_le h₁, truncate_apply_of_norm_le h₂]
  · rw [truncate_apply_of_not_norm_le h₁]
    by_cases h₂ : ‖g y‖ ≤ (s : ℝ)
    · rw [truncate_apply_of_norm_le h₂]
    · rw [truncate_apply_of_not_norm_le h₂]
      simp
theorem mul_conjFn_truncate_apply (g : Y → ℂ) (r : ℕ) (y : Y) :
    (g * conjFn (truncate g r)) y = ((‖truncate g r y‖ ^ 2 : ℝ) : ℂ) := by
  by_cases hy : ‖g y‖ ≤ (r : ℝ)
  · simp only [Pi.mul_apply, conjFn, truncate_apply_of_norm_le hy]
    rw [Complex.mul_conj, Complex.normSq_eq_norm_sq]
  · simp [conjFn, truncate_apply_of_not_norm_le hy]
theorem norm_sub_sq_le_two_mul (a b : ℂ) : ‖a - b‖ ^ 2 ≤ 2 * ‖a‖ ^ 2 + 2 * ‖b‖ ^ 2 := by
  have h₂ := pow_le_pow_left₀ (norm_nonneg _) (norm_sub_le a b) 2
  nlinarith [sq_nonneg (‖a‖ - ‖b‖)]
omit [InnerProductSpace ℂ H] [CompleteSpace H] in
theorem norm_add_sq_le_two_mul (x y : H) : ‖x + y‖ ^ 2 ≤ 2 * ‖x‖ ^ 2 + 2 * ‖y‖ ^ 2 := by
  have h₂ := pow_le_pow_left₀ (norm_nonneg _) (norm_add_le x y) 2
  nlinarith [sq_nonneg (‖x‖ - ‖y‖)]
theorem diagMeasure_add_le (E : SpectralMeasure Y H) (ψ φ : H) :
    E.diagMeasure (ψ + φ) ≤ (2 : ℝ≥0∞) • E.diagMeasure ψ + (2 : ℝ≥0∞) • E.diagMeasure φ := by
  rw [Measure.le_iff]
  intro s hs
  have h₁ := E.diagMeasure_apply (ψ + φ) ⟨s, hs⟩
  have h₂ := E.diagMeasure_apply ψ ⟨s, hs⟩
  have h₃ := E.diagMeasure_apply φ ⟨s, hs⟩
  dsimp only at h₁ h₂ h₃
  rw [Measure.add_apply, Measure.smul_apply, Measure.smul_apply, h₁, h₂, h₃, smul_eq_mul,
    smul_eq_mul]
  have two : (2 : ℝ≥0∞) = ENNReal.ofReal 2 := by simp
  rw [two, ← ENNReal.ofReal_mul (by norm_num), ← ENNReal.ofReal_mul (by norm_num),
    ← ENNReal.ofReal_add (by positivity) (by positivity)]
  refine ENNReal.ofReal_le_ofReal ?_
  rw [map_add]
  exact norm_add_sq_le_two_mul _ _
theorem diagMeasure_smul_le (E : SpectralMeasure Y H) (z : ℂ) (ψ : H) :
    E.diagMeasure (z • ψ) ≤ ENNReal.ofReal (‖z‖ ^ 2) • E.diagMeasure ψ := by
  rw [Measure.le_iff]
  intro s hs
  have h₁ := E.diagMeasure_apply (z • ψ) ⟨s, hs⟩
  have h₂ := E.diagMeasure_apply ψ ⟨s, hs⟩
  dsimp only at h₁ h₂
  rw [Measure.smul_apply, h₁, h₂, smul_eq_mul, ← ENNReal.ofReal_mul (by positivity)]
  refine ENNReal.ofReal_le_ofReal (le_of_eq ?_)
  rw [map_smul, norm_smul, mul_pow]
theorem add_mem_integralDom (hψ : ψ ∈ E.integralDom g) (hφ : φ ∈ E.integralDom g) :
    ψ + φ ∈ E.integralDom g := by
  show ∫⁻ y, ‖g y‖ₑ ^ 2 ∂E.diagMeasure (ψ + φ) < ∞
  refine (lintegral_mono' (diagMeasure_add_le E ψ φ) le_rfl).trans_lt ?_
  rw [lintegral_add_measure, lintegral_smul_measure, lintegral_smul_measure, smul_eq_mul,
    smul_eq_mul]
  exact ENNReal.add_lt_top.mpr ⟨ENNReal.mul_lt_top (by simp) hψ, ENNReal.mul_lt_top (by simp) hφ⟩
theorem smul_mem_integralDom (z : ℂ) (hψ : ψ ∈ E.integralDom g) : z • ψ ∈ E.integralDom g := by
  show ∫⁻ y, ‖g y‖ₑ ^ 2 ∂E.diagMeasure (z • ψ) < ∞
  refine (lintegral_mono' (diagMeasure_smul_le E z ψ) le_rfl).trans_lt ?_
  rw [lintegral_smul_measure, smul_eq_mul]
  exact ENNReal.mul_lt_top ENNReal.ofReal_lt_top hψ
theorem zero_mem_integralDom (g : Y → ℂ) : (0 : H) ∈ E.integralDom g := by
  show ∫⁻ y, ‖g y‖ₑ ^ 2 ∂E.diagMeasure (0 : H) < ∞
  have h := lintegral_mono' (f := fun y => ‖g y‖ₑ ^ 2) (diagMeasure_smul_le E 0 (0 : H)) le_rfl
  simpa using h.trans_lt (by simp)
theorem mem_integralDom_of_isBoundedFn (hb : IsBoundedFn g) (ψ : H) : ψ ∈ E.integralDom g := by
  obtain ⟨c, hc⟩ := hb
  rw [E.integralDom_eq_univ hc]
  exact mem_univ ψ
theorem mem_integralDom_of_norm_le {C : ℝ} (hle : ∀ᵐ y ∂E.diagMeasure ψ, ‖g y‖ ≤ C * ‖k y‖)
    (hψ : ψ ∈ E.integralDom k) : ψ ∈ E.integralDom g := by
  show ∫⁻ y, ‖g y‖ₑ ^ 2 ∂E.diagMeasure ψ < ∞
  have h₁ : ∀ᵐ y ∂E.diagMeasure ψ, ‖g y‖ₑ ^ 2 ≤ ENNReal.ofReal (C ^ 2) * ‖k y‖ₑ ^ 2 := by
    filter_upwards [hle] with y hy
    rw [← ofReal_norm, ← ofReal_norm, ← ENNReal.ofReal_pow (norm_nonneg _),
      ← ENNReal.ofReal_pow (norm_nonneg _), ← ENNReal.ofReal_mul (by positivity)]
    refine ENNReal.ofReal_le_ofReal ?_
    have := pow_le_pow_left₀ (norm_nonneg _) hy 2
    rwa [mul_pow] at this
  refine (lintegral_mono_ae h₁).trans_lt ?_
  rw [lintegral_const_mul' _ _ ENNReal.ofReal_ne_top]
  exact ENNReal.mul_lt_top ENNReal.ofReal_lt_top hψ
theorem ae_mem_of_isCarriedBy {Δ₀ : BorelSubsets Y} (hcar : E.IsCarriedBy Δ₀) (ψ : H) :
    ∀ᵐ y ∂E.diagMeasure ψ, y ∈ Δ₀.1 := by
  have h₀ : E.diagMeasure ψ Δ₀.1ᶜ = 0 := by
    have h₁ := E.diagMeasure_apply ψ ⟨Δ₀.1ᶜ, Δ₀.2.compl⟩
    have h₂ : E ⟨Δ₀.1ᶜ, Δ₀.2.compl⟩ = 0 := hcar
    rw [h₂] at h₁
    simpa using h₁
  filter_upwards [compl_mem_ae_iff.mpr h₀] with y hy
  simpa using hy
theorem integrable_norm_sq (hg : Measurable g) (hψ : ψ ∈ E.integralDom g) :
    Integrable (fun y => ‖g y‖ ^ 2) (E.diagMeasure ψ) := by
  have h : ∫⁻ y, ‖g y‖ₑ ^ 2 ∂E.diagMeasure ψ < ∞ := hψ
  refine ⟨(hg.norm.pow_const 2).aestronglyMeasurable, ?_⟩
  rw [hasFiniteIntegral_iff_enorm]
  simpa [enorm_pow] using h
theorem lintegral_enorm_sq_eq_ofReal {μ : Measure Y} (hi : Integrable (fun y => ‖g y‖ ^ 2) μ) :
    ∫⁻ y, ‖g y‖ₑ ^ 2 ∂μ = ENNReal.ofReal (∫ y, ‖g y‖ ^ 2 ∂μ) := by
  rw [ofReal_integral_eq_lintegral_ofReal hi (Eventually.of_forall fun _ => by positivity)]
  refine lintegral_congr fun y => ?_
  rw [ENNReal.ofReal_pow (norm_nonneg _), ofReal_norm]
theorem integrable_norm_sub_sq {μ : Measure Y} (hg : Measurable g) (hk : Measurable k)
    (hgi : Integrable (fun y => ‖g y‖ ^ 2) μ) (hki : Integrable (fun y => ‖k y‖ ^ 2) μ) :
    Integrable (fun y => ‖g y - k y‖ ^ 2) μ := by
  refine Integrable.mono' ((hgi.const_mul 2).add (hki.const_mul 2))
    ((hg.sub hk).norm.pow_const 2).aestronglyMeasurable (Eventually.of_forall fun y => ?_)
  rw [Real.norm_of_nonneg (by positivity)]
  exact norm_sub_sq_le_two_mul _ _
theorem tendsto_integral_norm_sub_sq {μ : Measure Y} {f : ℕ → Y → ℂ} {G : Y → ℂ}
    (hf : ∀ r, Measurable (f r)) (hk : Measurable k)
    (hGi : Integrable (fun y => ‖G y‖ ^ 2) μ) (hki : Integrable (fun y => ‖k y‖ ^ 2) μ)
    (hle : ∀ r y, ‖f r y‖ ≤ ‖G y‖) (hlim : ∀ y, Tendsto (fun r => f r y) atTop (𝓝 (G y))) :
    Tendsto (fun r => ∫ y, ‖f r y - k y‖ ^ 2 ∂μ) atTop (𝓝 (∫ y, ‖G y - k y‖ ^ 2 ∂μ)) := by
  refine tendsto_integral_of_dominated_convergence (fun y => 2 * ‖G y‖ ^ 2 + 2 * ‖k y‖ ^ 2)
    (fun r => (((hf r).sub hk).norm.pow_const 2).aestronglyMeasurable)
    ((hGi.const_mul 2).add (hki.const_mul 2))
    (fun r => Eventually.of_forall fun y => ?_)
    (Eventually.of_forall fun y => ((hlim y).sub_const (k y)).norm.pow 2)
  rw [Real.norm_of_nonneg (by positivity)]
  have h₁ := norm_sub_sq_le_two_mul (f r y) (k y)
  have h₂ := pow_le_pow_left₀ (norm_nonneg _) (hle r y) 2
  linarith
theorem isDiagonalIntegral_integralOp (hE : BoundedFunctionalCalculus E) (hg : Measurable g)
    (hb : IsBoundedFn g) : E.IsDiagonalIntegral g (E.integralOp g) :=
  Classical.epsilon_spec (hE.existsUnique_op g hg hb).exists
theorem isBoundedFn_sub (hg : IsBoundedFn g) (hk : IsBoundedFn k) :
    IsBoundedFn (g - k) := by
  obtain ⟨a, ha⟩ := hg
  obtain ⟨b, hb⟩ := hk
  exact ⟨a + b, fun y => (norm_sub_le _ _).trans (add_le_add (ha y) (hb y))⟩
theorem integralOp_sub (hE : BoundedFunctionalCalculus E) (hg : Measurable g)
    (hgb : IsBoundedFn g) (hk : Measurable k) (hkb : IsBoundedFn k) :
    E.integralOp (g - k) = E.integralOp g - E.integralOp k := by
  have e : g - k = g + (-1 : ℂ) • k := by
    funext y
    simp [sub_eq_add_neg]
  have hnk : Measurable ((-1 : ℂ) • k) := hk.const_smul _
  have hnkb : IsBoundedFn ((-1 : ℂ) • k) := by
    obtain ⟨c, hc⟩ := hkb
    exact ⟨c, fun y => by simpa using hc y⟩
  rw [e, hE.add _ _ hg hgb hnk hnkb, hE.smul _ _ hk hkb]
  simp [sub_eq_add_neg]
theorem norm_integralOp_sub_sq (hE : BoundedFunctionalCalculus E) (hg : Measurable g)
    (hgb : IsBoundedFn g) (hk : Measurable k) (hkb : IsBoundedFn k) (ψ : H) :
    ‖E.integralOp g ψ - E.integralOp k ψ‖ ^ 2 =
      ∫ y, ‖g y - k y‖ ^ 2 ∂E.diagMeasure ψ := by
  have h := hE.norm_sq (g - k) (hg.sub hk) (isBoundedFn_sub hgb hkb) ψ
  rw [integralOp_sub hE hg hgb hk hkb] at h
  simpa using h
theorem integralOp_zero (hE : BoundedFunctionalCalculus E) : E.integralOp (0 : Y → ℂ) = 0 := by
  have h := hE.smul 0 0 measurable_const ⟨0, fun _ => by simp⟩
  simpa using h
theorem integralOp_one (hE : BoundedFunctionalCalculus E) : E.integralOp (1 : Y → ℂ) = 1 := by
  have h := hE.indicator ⟨univ, MeasurableSet.univ⟩
  rw [E.map_univ] at h
  simpa using h
theorem lintegral_diagMeasure_integralOp (hE : BoundedFunctionalCalculus E) (hh : Measurable h)
    (hhb : IsBoundedFn h) (ψ : H) {f : Y → ℝ≥0∞} (hf : Measurable f) :
    ∫⁻ y, f y ∂E.diagMeasure (E.integralOp h ψ) =
      ∫⁻ y, ‖h y‖ₑ ^ 2 * f y ∂E.diagMeasure ψ := by
  have hμ : E.diagMeasure (E.integralOp h ψ) =
      (E.diagMeasure ψ).withDensity fun y => ‖h y‖ₑ ^ 2 := by
    refine Measure.ext fun Δ hΔ => ?_
    rw [withDensity_apply _ hΔ]
    exact hE.diagMeasure_eq h hh hhb ψ ⟨Δ, hΔ⟩
  rw [hμ, lintegral_withDensity_eq_lintegral_mul _ (hh.enorm.pow_const 2) hf]
  rfl
theorem integralOp_mem_iff (hE : BoundedFunctionalCalculus E) (hg : Measurable g) (hh : Measurable h)
    (hhb : IsBoundedFn h) :
    E.integralOp h ψ ∈ E.integralDom g ↔ ψ ∈ E.integralDom (g * h) := by
  show ∫⁻ y, ‖g y‖ₑ ^ 2 ∂E.diagMeasure (E.integralOp h ψ) < ∞ ↔
    ∫⁻ y, ‖(g * h) y‖ₑ ^ 2 ∂E.diagMeasure ψ < ∞
  rw [lintegral_diagMeasure_integralOp hE hh hhb ψ (hg.enorm.pow_const 2)]
  have : ∀ y, ‖h y‖ₑ ^ 2 * ‖g y‖ₑ ^ 2 = ‖(g * h) y‖ₑ ^ 2 := fun y => by
    rw [Pi.mul_apply, enorm_mul, mul_pow, mul_comm]
  simp only [this]
theorem mem_integralDom_mul (hhb : IsBoundedFn h) (hψ : ψ ∈ E.integralDom g) :
    ψ ∈ E.integralDom (g * h) := by
  obtain ⟨c, hc⟩ := hhb
  refine mem_integralDom_of_norm_le (C := |c|) (Eventually.of_forall fun y => ?_) hψ
  rw [Pi.mul_apply, norm_mul, mul_comm]
  exact mul_le_mul_of_nonneg_right ((hc y).trans (le_abs_self c)) (norm_nonneg _)
theorem tendsto_integralOp_truncate (hE : BoundedFunctionalCalculus E) (hg : Measurable g)
    (hψ : ψ ∈ E.integralDom g) :
    Tendsto (fun r => E.integralOp (truncate g r) ψ) atTop (𝓝 (E.integralApply g ψ)) := by
  have hgi := integrable_norm_sq hg hψ
  have ht := measurable_truncate hg
  have ha := tendsto_integral_norm_sub_sq (μ := E.diagMeasure ψ) ht hg hgi hgi
    (norm_truncate_apply_le_norm g) (tendsto_truncate_apply g)
  have hz : ∫ y, ‖g y - g y‖ ^ 2 ∂E.diagMeasure ψ = 0 := by simp
  rw [hz] at ha
  have hc : CauchySeq fun r => E.integralOp (truncate g r) ψ := by
    refine cauchySeq_of_le_tendsto_0'
      (fun r => Real.sqrt (∫ y, ‖truncate g r y - g y‖ ^ 2 ∂E.diagMeasure ψ))
      (fun r s hrs => ?_) (by simpa using ha.sqrt)
    have hd : dist (E.integralOp (truncate g r) ψ) (E.integralOp (truncate g s) ψ) =
        Real.sqrt (‖E.integralOp (truncate g r) ψ -
          E.integralOp (truncate g s) ψ‖ ^ 2) := by
      rw [dist_eq_norm, Real.sqrt_sq (norm_nonneg _)]
    rw [hd]
    refine Real.sqrt_le_sqrt ?_
    rw [norm_integralOp_sub_sq hE (ht r) (isBoundedFn_truncate g r) (ht s)
      (isBoundedFn_truncate g s)]
    exact integral_mono_of_nonneg (Eventually.of_forall fun y => by
        simp only [Pi.zero_apply]
        positivity)
      (integrable_norm_sub_sq (ht r) hg
        (integrable_norm_sq (ht r) (mem_integralDom_of_isBoundedFn (isBoundedFn_truncate g r) ψ)) hgi)
      (Eventually.of_forall (norm_truncate_sub_truncate_sq_le g hrs))
  obtain ⟨L, hL⟩ := cauchySeq_tendsto_of_complete hc
  have hv : E.integralApply g ψ = L := hL.limUnder_eq
  rwa [hv]
theorem norm_integralApply_sub_sq (hE : BoundedFunctionalCalculus E) (hg : Measurable g)
    (hh : Measurable h) (hhb : IsBoundedFn h) (hψ : ψ ∈ E.integralDom g) :
    ‖E.integralApply g ψ - E.integralOp h ψ‖ ^ 2 = ∫ y, ‖g y - h y‖ ^ 2 ∂E.diagMeasure ψ := by
  have ht := measurable_truncate hg
  refine tendsto_nhds_unique (((tendsto_integralOp_truncate hE hg hψ).sub_const _).norm.pow 2) ?_
  refine (tendsto_integral_norm_sub_sq (μ := E.diagMeasure ψ) ht hh (integrable_norm_sq hg hψ)
    (integrable_norm_sq hh (mem_integralDom_of_isBoundedFn hhb ψ)) (norm_truncate_apply_le_norm g)
    (tendsto_truncate_apply g)).congr fun r => ?_
  exact (norm_integralOp_sub_sq hE (ht r) (isBoundedFn_truncate g r) hh hhb ψ).symm
theorem norm_integralApply_sq (hE : BoundedFunctionalCalculus E) (hg : Measurable g)
    (hψ : ψ ∈ E.integralDom g) :
    ‖E.integralApply g ψ‖ ^ 2 = ∫ y, ‖g y‖ ^ 2 ∂E.diagMeasure ψ := by
  have h := norm_integralApply_sub_sq (h := 0) hE hg measurable_const ⟨0, fun _ => by simp⟩ hψ
  simpa [integralOp_zero hE] using h
theorem inner_self_integralApply (hE : BoundedFunctionalCalculus E) (hg : Measurable g)
    (hψ : ψ ∈ E.integralDom g) :
    ⟪ψ, E.integralApply g ψ⟫_ℂ = ∫ y, g y ∂E.diagMeasure ψ := by
  have ht := measurable_truncate hg
  have hint : Integrable g (E.diagMeasure ψ) :=
    ((memLp_two_iff_integrable_sq_norm hg.aestronglyMeasurable).mpr
      (integrable_norm_sq hg hψ)).integrable one_le_two
  have h₁ : Tendsto (fun r => ⟪ψ, E.integralOp (truncate g r) ψ⟫_ℂ) atTop
      (𝓝 ⟪ψ, E.integralApply g ψ⟫_ℂ) :=
    tendsto_const_nhds.inner (tendsto_integralOp_truncate hE hg hψ)
  refine tendsto_nhds_unique h₁ ?_
  refine (tendsto_integral_of_dominated_convergence (μ := E.diagMeasure ψ)
    (F := fun r y => truncate g r y) (f := g) (fun y => ‖g y‖)
    (fun r => (ht r).aestronglyMeasurable) hint.norm
    (fun r => Eventually.of_forall (norm_truncate_apply_le_norm g r))
    (Eventually.of_forall (tendsto_truncate_apply g))).congr fun r => ?_
  exact (isDiagonalIntegral_integralOp hE (ht r) (isBoundedFn_truncate g r) ψ).symm
theorem integralApply_add (hE : BoundedFunctionalCalculus E) (hg : Measurable g)
    (hψ : ψ ∈ E.integralDom g) (hφ : φ ∈ E.integralDom g) :
    E.integralApply g (ψ + φ) = E.integralApply g ψ + E.integralApply g φ := by
  refine tendsto_nhds_unique (tendsto_integralOp_truncate hE hg (add_mem_integralDom hψ hφ)) ?_
  simpa only [map_add] using
    (tendsto_integralOp_truncate hE hg hψ).add (tendsto_integralOp_truncate hE hg hφ)
theorem integralApply_smul (hE : BoundedFunctionalCalculus E) (hg : Measurable g) (z : ℂ)
    (hψ : ψ ∈ E.integralDom g) :
    E.integralApply g (z • ψ) = z • E.integralApply g ψ := by
  refine tendsto_nhds_unique (tendsto_integralOp_truncate hE hg (smul_mem_integralDom z hψ)) ?_
  simpa only [map_smul] using (tendsto_integralOp_truncate hE hg hψ).const_smul z
def integralDomSubmodule (E : SpectralMeasure Y H) (g : Y → ℂ) : Submodule ℂ H where
  carrier := E.integralDom g
  add_mem' := add_mem_integralDom
  zero_mem' := zero_mem_integralDom g
  smul_mem' z _ h := smul_mem_integralDom z h
def integralOperator (hE : BoundedFunctionalCalculus E) (hg : Measurable g) : UnboundedOp H :=
  ⟨integralDomSubmodule E g,
    { toFun := fun ψ => E.integralApply g ψ
      map_add' := fun ψ φ => integralApply_add hE hg ψ.2 φ.2
      map_smul' := fun z ψ => integralApply_smul hE hg z ψ.2 }⟩
theorem isCarriedBy_univ (hE : BoundedFunctionalCalculus E) :
    E.IsCarriedBy ⟨univ, MeasurableSet.univ⟩ := by
  have hu : (⟨(univ : Set Y)ᶜ, MeasurableSet.univ.compl⟩ : BorelSubsets Y) =
      ⟨∅, MeasurableSet.empty⟩ := Subtype.ext compl_univ
  exact (congrArg E.toFun hu).trans hE.apply_empty
theorem integralApply_integralOp_of_isBoundedFn (hE : BoundedFunctionalCalculus E)
    (hS : StrongConvergence E) (hg : Measurable g) (hh : Measurable h) (hhb : IsBoundedFn h)
    (hgh : IsBoundedFn (g * h)) (ψ : H) :
    E.integralOp h ψ ∈ E.integralDom g ∧
      E.integralApply g (E.integralOp h ψ) = E.integralOp (g * h) ψ := by
  have hmem : E.integralOp h ψ ∈ E.integralDom g :=
    (integralOp_mem_iff hE hg hh hhb).mpr (mem_integralDom_of_isBoundedFn hgh ψ)
  refine ⟨hmem, tendsto_nhds_unique (tendsto_integralOp_truncate hE hg hmem) ?_⟩
  have ht := measurable_truncate hg
  obtain ⟨c, hc⟩ := hgh
  have hle : ∀ r y, ‖(truncate g r * h) y‖ ≤ c := fun r y => by
    refine le_trans ?_ (hc y)
    rw [Pi.mul_apply, Pi.mul_apply, norm_mul, norm_mul]
    exact mul_le_mul_of_nonneg_right (norm_truncate_apply_le_norm g r y) (norm_nonneg _)
  have hlim := (hS (fun r => truncate g r * h) (g * h) c ⟨univ, MeasurableSet.univ⟩
    (fun r => (ht r).mul hh) (hg.mul hh) hle (isCarriedBy_univ hE)
    (fun y _ => (tendsto_truncate_apply g y).mul_const (h y))).2 ψ
  rw [E.integralApply_eq_integralOp hc] at hlim
  refine hlim.congr fun r => ?_
  rw [hE.mul _ _ (ht r) (isBoundedFn_truncate g r) hh hhb]
  rfl
theorem integralApply_integralOp_comm (hE : BoundedFunctionalCalculus E) (hg : Measurable g)
    (hh : Measurable h) (hhb : IsBoundedFn h) (hψ : ψ ∈ E.integralDom g) :
    E.integralApply g (E.integralOp h ψ) = E.integralOp h (E.integralApply g ψ) := by
  have hmem : E.integralOp h ψ ∈ E.integralDom g :=
    (integralOp_mem_iff hE hg hh hhb).mpr (mem_integralDom_mul hhb hψ)
  have ht := measurable_truncate hg
  refine tendsto_nhds_unique (tendsto_integralOp_truncate hE hg hmem) ?_
  refine (((E.integralOp h).continuous.tendsto _).comp (tendsto_integralOp_truncate hE hg hψ)).congr
    fun r => ?_
  have h₁ := hE.mul _ _ (ht r) (isBoundedFn_truncate g r) hh hhb
  have h₂ := hE.mul _ _ hh hhb (ht r) (isBoundedFn_truncate g r)
  rw [mul_comm (truncate g r) h, h₂] at h₁
  exact congrArg (fun T : H →L[ℂ] H => T ψ) h₁
theorem integralApply_integralOp_eq_mul (hE : BoundedFunctionalCalculus E) (hg : Measurable g)
    (hh : Measurable h) (hhb : IsBoundedFn h) (hψ : ψ ∈ E.integralDom g) :
    ψ ∈ E.integralDom (g * h) ∧
      E.integralApply g (E.integralOp h ψ) = E.integralApply (g * h) ψ := by
  have hgh := mem_integralDom_mul hhb hψ
  have hmem : E.integralOp h ψ ∈ E.integralDom g :=
    (integralOp_mem_iff hE hg hh hhb).mpr hgh
  refine ⟨hgh, tendsto_nhds_unique (tendsto_integralOp_truncate hE hg hmem) ?_⟩
  have ht := measurable_truncate hg
  have hm : ∀ r, Measurable (truncate g r * h) := fun r => (ht r).mul hh
  have hb : ∀ r, IsBoundedFn (truncate g r * h) := fun r => by
    obtain ⟨c, hc⟩ := hhb
    refine ⟨r * |c|, fun y => ?_⟩
    rw [Pi.mul_apply, norm_mul]
    exact mul_le_mul (norm_truncate_apply_le g r y) ((hc y).trans (le_abs_self c)) (norm_nonneg _)
      (by positivity)
  have hGi := integrable_norm_sq (hg.mul hh) hgh
  have hlim := tendsto_integral_norm_sub_sq (μ := E.diagMeasure ψ) hm (hg.mul hh) hGi hGi
    (fun r y => by
      rw [Pi.mul_apply, Pi.mul_apply, norm_mul, norm_mul]
      exact mul_le_mul_of_nonneg_right (norm_truncate_apply_le_norm g r y) (norm_nonneg _))
    (fun y => (tendsto_truncate_apply g y).mul_const (h y))
  have hz : ∫ y, ‖(g * h) y - (g * h) y‖ ^ 2 ∂E.diagMeasure ψ = 0 := by simp
  rw [hz] at hlim
  have hn : Tendsto (fun r => ‖E.integralOp (truncate g r) (E.integralOp h ψ) -
      E.integralApply (g * h) ψ‖) atTop (𝓝 0) := by
    have hs := hlim.sqrt
    rw [Real.sqrt_zero] at hs
    refine hs.congr fun r => ?_
    have h₁ := norm_integralApply_sub_sq hE (hg.mul hh) (hm r) (hb r) hgh
    have h₂ : E.integralOp (truncate g r) (E.integralOp h ψ) =
        E.integralOp (truncate g r * h) ψ := by
      rw [hE.mul _ _ (ht r) (isBoundedFn_truncate g r) hh hhb]
      rfl
    rw [h₂, norm_sub_rev, ← Real.sqrt_sq (norm_nonneg (E.integralApply (g * h) ψ -
      E.integralOp (truncate g r * h) ψ)), h₁]
    simp only [norm_sub_rev]
  exact tendsto_iff_norm_sub_tendsto_zero.mpr hn
theorem dense_integralDom (hE : BoundedFunctionalCalculus E) (hS : StrongConvergence E)
    (hg : Measurable g) : Dense (E.integralDom g) := by
  intro ψ
  obtain ⟨χ, hχ⟩ : ∃ χ : ℕ → Y → ℂ, χ = fun r : ℕ => {y | ‖g y‖ ≤ (r : ℝ)}.indicator 1 := ⟨_, rfl⟩
  have hset : ∀ r : ℕ, MeasurableSet {y | ‖g y‖ ≤ (r : ℝ)} := fun r =>
    measurableSet_le hg.norm measurable_const
  have hm : ∀ r, Measurable (χ r) := fun r => by
    rw [hχ]
    exact measurable_one.indicator (hset r)
  have hχ1 : ∀ r y, ‖χ r y‖ ≤ 1 := fun r y => by
    rw [hχ]
    by_cases hy : ‖g y‖ ≤ (r : ℝ)
    · simp [indicator_of_mem (show y ∈ {y | ‖g y‖ ≤ (r : ℝ)} from hy)]
    · simp [indicator_of_notMem (show y ∉ {y | ‖g y‖ ≤ (r : ℝ)} from hy)]
  have hχg : ∀ r y, ‖(g * χ r) y‖ ≤ r := fun r y => by
    rw [hχ]
    by_cases hy : ‖g y‖ ≤ (r : ℝ)
    · simpa [indicator_of_mem (show y ∈ {y | ‖g y‖ ≤ (r : ℝ)} from hy)] using hy
    · simp [indicator_of_notMem (show y ∉ {y | ‖g y‖ ≤ (r : ℝ)} from hy)]
  have hlimit : ∀ y, Tendsto (fun r => χ r y) atTop (𝓝 ((1 : Y → ℂ) y)) := fun y => by
    refine tendsto_const_nhds.congr' ?_
    obtain ⟨r₀, hr₀⟩ := exists_nat_ge ‖g y‖
    filter_upwards [eventually_ge_atTop r₀] with r hr
    have hy : ‖g y‖ ≤ (r : ℝ) := hr₀.trans (by exact_mod_cast hr)
    rw [hχ]
    simp [indicator_of_mem (show y ∈ {y | ‖g y‖ ≤ (r : ℝ)} from hy)]
  have h₁ := (hS χ 1 1 ⟨univ, MeasurableSet.univ⟩ hm measurable_one hχ1 (isCarriedBy_univ hE)
    (fun y _ => hlimit y)).2 ψ
  rw [E.integralApply_eq_integralOp (c := 1) (fun _ => by simp), integralOp_one hE] at h₁
  refine mem_closure_of_tendsto h₁ (Eventually.of_forall fun r => ?_)
  exact (integralOp_mem_iff hE hg (hm r) ⟨1, hχ1 r⟩).mpr
    (mem_integralDom_of_isBoundedFn ⟨r, hχg r⟩ ψ)
theorem measurable_conjFn (hg : Measurable g) : Measurable (conjFn g) :=
  Complex.continuous_conj.measurable.comp hg
theorem mem_integralDom_conjFn (hψ : ψ ∈ E.integralDom g) :
    ψ ∈ E.integralDom (conjFn g) :=
  mem_integralDom_of_norm_le (C := 1) (Eventually.of_forall fun y => by simp [conjFn]) hψ
theorem inner_integralApply_eq (hE : BoundedFunctionalCalculus E) (hg : Measurable g)
    (hφ : φ ∈ E.integralDom (conjFn g)) (hψ : ψ ∈ E.integralDom g) :
    ⟪φ, E.integralApply g ψ⟫_ℂ = ⟪E.integralApply (conjFn g) φ, ψ⟫_ℂ := by
  have ht := measurable_truncate hg
  have h₁ : Tendsto (fun r => ⟪φ, E.integralOp (truncate g r) ψ⟫_ℂ) atTop
      (𝓝 ⟪φ, E.integralApply g ψ⟫_ℂ) :=
    tendsto_const_nhds.inner (tendsto_integralOp_truncate hE hg hψ)
  have h₂ : Tendsto (fun r => ⟪E.integralOp (truncate (conjFn g) r) φ, ψ⟫_ℂ) atTop
      (𝓝 ⟪E.integralApply (conjFn g) φ, ψ⟫_ℂ) :=
    (tendsto_integralOp_truncate hE (measurable_conjFn hg) hφ).inner tendsto_const_nhds
  refine tendsto_nhds_unique h₁ (h₂.congr fun r => ?_)
  rw [truncate_conjFn, hE.star_eq _ (ht r) (isBoundedFn_truncate g r),
    ContinuousLinearMap.star_eq_adjoint, ContinuousLinearMap.adjoint_inner_left]
theorem mem_integralDom_of_adjoint (hE : BoundedFunctionalCalculus E) (hS : StrongConvergence E)
    (hg : Measurable g) {η : H}
    (hη : ∀ ψ ∈ E.integralDom g, ⟪φ, E.integralApply g ψ⟫_ℂ = ⟪η, ψ⟫_ℂ) :
    φ ∈ E.integralDom g := by
  have ht := measurable_truncate hg
  have key : ∀ r, ∫⁻ y, ‖truncate g r y‖ₑ ^ 2 ∂E.diagMeasure φ ≤ ENNReal.ofReal (‖η‖ ^ 2) := by
    intro r
    obtain ⟨k, hk⟩ : ∃ k, k = conjFn (truncate g r) := ⟨_, rfl⟩
    have hkm : Measurable k := hk ▸ measurable_conjFn (ht r)
    have hnk : ∀ y, ‖k y‖ = ‖truncate g r y‖ := fun y => by simp [hk, conjFn]
    have hkb : IsBoundedFn k := ⟨r, fun y => (hnk y).trans_le (norm_truncate_apply_le g r y)⟩
    have hp : ∀ y, (g * k) y = ((‖truncate g r y‖ ^ 2 : ℝ) : ℂ) := fun y => by
      rw [hk]
      exact mul_conjFn_truncate_apply g r y
    have hpb : IsBoundedFn (g * k) := by
      refine ⟨(r : ℝ) ^ 2, fun y => ?_⟩
      rw [hp y, Complex.norm_real, Real.norm_of_nonneg (by positivity)]
      exact pow_le_pow_left₀ (norm_nonneg _) (norm_truncate_apply_le g r y) 2
    obtain ⟨hmem, hval⟩ := integralApply_integralOp_of_isBoundedFn hE hS hg hkm hkb hpb φ
    have hti : Integrable (fun y => ‖truncate g r y‖ ^ 2) (E.diagMeasure φ) :=
      integrable_norm_sq (ht r) (mem_integralDom_of_isBoundedFn (isBoundedFn_truncate g r) φ)
    obtain ⟨I, hI⟩ : ∃ I, I = ∫ y, ‖truncate g r y‖ ^ 2 ∂E.diagMeasure φ := ⟨_, rfl⟩
    have hI0 : 0 ≤ I := hI ▸ integral_nonneg fun y => by positivity
    have h₁ : (I : ℂ) = ⟪η, E.integralOp k φ⟫_ℂ := by
      rw [← hη _ hmem, hval, isDiagonalIntegral_integralOp hE (hg.mul hkm) hpb φ, hI]
      simp_rw [hp]
      exact (integral_ofReal).symm
    have h₂ : ‖E.integralOp k φ‖ ^ 2 = I := by
      rw [hE.norm_sq k hkm hkb φ, hI]
      simp_rw [hnk]
    have h₃ : I ≤ ‖η‖ * ‖E.integralOp k φ‖ := by
      have h₄ := norm_inner_le_norm (𝕜 := ℂ) η (E.integralOp k φ)
      rw [← h₁, Complex.norm_real, Real.norm_of_nonneg hI0] at h₄
      exact h₄
    have h₅ : ‖E.integralOp k φ‖ ≤ ‖η‖ := by
      by_contra hlt
      have hlt' := not_le.mp hlt
      have hpos : 0 < ‖E.integralOp k φ‖ := (norm_nonneg η).trans_lt hlt'
      nlinarith
    rw [lintegral_enorm_sq_eq_ofReal hti, ← hI, ← h₂]
    exact ENNReal.ofReal_le_ofReal (pow_le_pow_left₀ (norm_nonneg _) h₅ 2)
  have hfat : ∫⁻ y, liminf (fun r => ‖truncate g r y‖ₑ ^ 2) atTop ∂E.diagMeasure φ ≤
      liminf (fun r => ∫⁻ y, ‖truncate g r y‖ₑ ^ 2 ∂E.diagMeasure φ) atTop :=
    lintegral_liminf_le fun r => (ht r).enorm.pow_const 2
  have hlim : ∀ y, liminf (fun r => ‖truncate g r y‖ₑ ^ 2) atTop = ‖g y‖ₑ ^ 2 := fun y => by
    have h₁ : Tendsto (fun r => ‖truncate g r y‖ₑ ^ 2) atTop (𝓝 (‖g y‖ₑ ^ 2)) :=
      ENNReal.Tendsto.pow (tendsto_truncate_apply g y).enorm
    exact h₁.liminf_eq
  simp only [hlim] at hfat
  show ∫⁻ y, ‖g y‖ₑ ^ 2 ∂E.diagMeasure φ < ∞
  calc ∫⁻ y, ‖g y‖ₑ ^ 2 ∂E.diagMeasure φ
      ≤ liminf (fun r => ∫⁻ y, ‖truncate g r y‖ₑ ^ 2 ∂E.diagMeasure φ) atTop := hfat
    _ ≤ liminf (fun _ : ℕ => ENNReal.ofReal (‖η‖ ^ 2)) atTop :=
        liminf_le_liminf (Eventually.of_forall key)
    _ = ENNReal.ofReal (‖η‖ ^ 2) := liminf_const _
    _ < ∞ := ENNReal.ofReal_lt_top
theorem isAdjointOf_integral (hE : BoundedFunctionalCalculus E) (hS : StrongConvergence E)
    (hg : Measurable g) {A A' : UnboundedOp H}
    (hA : HasDomainAndAction A (E.integralDom g) (E.integralApply g))
    (hA' : HasDomainAndAction A' (E.integralDom (conjFn g))
      (E.integralApply (conjFn g))) : IsAdjointOf A' A := by
  have memA : ∀ ψ : A.domain, (ψ : H) ∈ E.integralDom g := fun ψ => by
    rw [← hA.1]
    exact ψ.2
  have memA' : ∀ φ : A'.domain, (φ : H) ∈ E.integralDom (conjFn g) := fun φ => by
    rw [← hA'.1]
    exact φ.2
  have hin : ∀ (φ : A'.domain) (ψ : A.domain), ⟪(φ : H), A ψ⟫_ℂ = ⟪A' φ, (ψ : H)⟫_ℂ :=
    fun φ ψ => by
      rw [hA.2 ψ, hA'.2 φ]
      exact inner_integralApply_eq hE hg (memA' φ) (memA ψ)
  refine ⟨fun φ => ⟨fun hφ => ⟨A' ⟨φ, hφ⟩, fun ψ => hin ⟨φ, hφ⟩ ψ⟩, ?_⟩, hin⟩
  rintro ⟨η, hη⟩
  have hD : φ ∈ E.integralDom g := by
    refine mem_integralDom_of_adjoint hE hS hg (η := η) fun ψ hψ => ?_
    have hψ' : ψ ∈ A.domain := by
      have : ψ ∈ (A.domain : Set H) := by
        rw [hA.1]
        exact hψ
      exact this
    have h₁ := hη ⟨ψ, hψ'⟩
    rwa [hA.2 ⟨ψ, hψ'⟩] at h₁
  have : φ ∈ (A'.domain : Set H) := by
    rw [hA'.1]
    exact mem_integralDom_conjFn hD
  exact this
theorem integralApply_congr (hE : BoundedFunctionalCalculus E) {g h' : Y → ℂ} (hg : Measurable g)
    (hh' : Measurable h') {Δ₀ : BorelSubsets Y} (hcar : E.IsCarriedBy Δ₀)
    (heq : ∀ y ∈ Δ₀.1, g y = h' y) (ψ : H) : E.integralApply g ψ = E.integralApply h' ψ := by
  have hs : (fun r => E.integralOp (truncate g r) ψ) =
      fun r => E.integralOp (truncate h' r) ψ := funext fun r => by
    have h₀ := norm_integralOp_sub_sq hE (measurable_truncate hg r)
      (isBoundedFn_truncate g r) (measurable_truncate hh' r) (isBoundedFn_truncate h' r) ψ
    have hz : ∫ y, ‖truncate g r y - truncate h' r y‖ ^ 2 ∂E.diagMeasure ψ = 0 := by
      refine integral_eq_zero_of_ae ?_
      filter_upwards [ae_mem_of_isCarriedBy hcar ψ] with y hy
      simp [truncate_apply_congr (heq y hy) r]
    rw [hz] at h₀
    exact sub_eq_zero.mp (norm_eq_zero.mp ((pow_eq_zero_iff two_ne_zero).mp h₀))
  show limUnder atTop _ = limUnder atTop _
  rw [hs]
theorem unboundedFunctionalCalculus (hE : BoundedFunctionalCalculus E) (hS : StrongConvergence E) :
    UnboundedFunctionalCalculus E where
  exists_op g hg :=
    ⟨integralOperator hE hg, dense_integralDom hE hS hg, rfl, fun _ => rfl⟩
  tendsto_truncate g hg ψ hψ := tendsto_integralOp_truncate hE hg hψ
  norm_sub_sq g h hg hh hhb ψ hψ := norm_integralApply_sub_sq hE hg hh hhb hψ
  norm_sq g hg ψ hψ := norm_integralApply_sq hE hg hψ
  inner_eq g hg ψ hψ := inner_self_integralApply hE hg hψ
  adjoint g hg A A' hA hA' := isAdjointOf_integral hE hS hg hA hA'
  isSelfAdjoint g hg hr A hA := by
    have hc : conjFn g = g := funext fun y => Complex.conj_eq_iff_im.mpr (hr y)
    refine ⟨?_, isAdjointOf_integral hE hS hg hA (by rwa [hc])⟩
    rw [hA.1]
    exact dense_integralDom hE hS hg
  integralOp_mem g h hg hh hhb ψ hψ :=
    (integralOp_mem_iff hE hg hh hhb).mpr (mem_integralDom_mul hhb hψ)
  integralApply_integralOp g h hg hh hhb ψ hψ := integralApply_integralOp_comm hE hg hh hhb hψ
  integralApply_mul g h hg hh hhb ψ hψ := integralApply_integralOp_eq_mul hE hg hh hhb hψ
  range_subset_dom g h hg hh hhb hgh ψ :=
    integralApply_integralOp_of_isBoundedFn hE hS hg hh hhb hgh ψ
  dom_subset g h' hg hh' Δ₀ hcar hle ψ hψ := by
    refine mem_integralDom_of_norm_le (C := 1) ?_ hψ
    filter_upwards [ae_mem_of_isCarriedBy hcar ψ] with y hy
    simpa using hle y hy
  congr g h' hg hh' Δ₀ hcar heq := by
    refine ⟨Subset.antisymm (fun ψ hψ => ?_) (fun ψ hψ => ?_),
      fun ψ _ => integralApply_congr hE hg hh' hcar heq ψ⟩
    · refine mem_integralDom_of_norm_le (C := 1) ?_ hψ
      filter_upwards [ae_mem_of_isCarriedBy hcar ψ] with y hy
      simp [heq y hy]
    · refine mem_integralDom_of_norm_le (C := 1) ?_ hψ
      filter_upwards [ae_mem_of_isCarriedBy hcar ψ] with y hy
      simp [heq y hy]
theorem unboundedFunctionalCalculusHolds
    (hB : YangMills.Construction.SpectralTheory.BoundedBorelCalculus.BoundedBorelCalculusHolds)
    (hL : YangMills.Construction.BorelCalculus.StrongConvergenceHolds) :
    YangMills.Construction.BorelCalculus.UnboundedFunctionalCalculusHolds :=
  fun H _ _ _ n Y E => unboundedFunctionalCalculus (hB H n Y E) (hL H n Y E)
end YangMills.Construction.BorelCalculus.Unbounded
