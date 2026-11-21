import YangMills.Construction.SpectralTheory.BoundedBorelCalculus
import YangMills.Construction.SpectralTheory.KernelAndPositivityOfSpectralIntegrals
import YangMills.Construction.SpectralTheory.UnboundedFunctionalCalculusStatement
import Mathlib
set_option autoImplicit false
open MeasureTheory Set Filter Topology
open scoped ENNReal InnerProductSpace ComplexOrder
noncomputable section
namespace YangMills.Construction.SpectralKernel
open BorelSpectral BorelCalculus
variable {n : ℕ} {Y : Set (Fin n → ℝ)} {H : Type} [NormedAddCommGroup H] [InnerProductSpace ℂ H]
  [CompleteSpace H]
theorem apply_compl_apply (E : SpectralMeasure Y H) (hE : BoundedFunctionalCalculus E)
    (Δ : BorelSubsets Y) (ψ : H) : E ⟨Δ.1ᶜ, Δ.2.compl⟩ ψ = ψ - E Δ ψ := by
  have hm : ∀ Δ' : BorelSubsets Y, Measurable (Δ'.1.indicator (1 : Y → ℂ)) :=
    fun Δ' => measurable_one.indicator Δ'.2
  have hb : ∀ Δ' : BorelSubsets Y, IsBoundedFn (Δ'.1.indicator (1 : Y → ℂ)) := fun Δ' =>
    ⟨1, fun y => by by_cases h : y ∈ Δ'.1 <;> simp [h]⟩
  have hsum : (⟨Δ.1ᶜ, Δ.2.compl⟩ : BorelSubsets Y).1.indicator (1 : Y → ℂ) + Δ.1.indicator 1 =
      (⟨univ, MeasurableSet.univ⟩ : BorelSubsets Y).1.indicator 1 := by
    funext y
    by_cases h : y ∈ Δ.1 <;> simp [h]
  have h₁ := hE.add _ _ (hm ⟨Δ.1ᶜ, Δ.2.compl⟩) (hb _) (hm Δ) (hb Δ)
  rw [hsum, hE.indicator, hE.indicator, hE.indicator, E.map_univ] at h₁
  have h₂ := congrArg (fun T : H →L[ℂ] H => T ψ) h₁
  simp only [add_apply, one_apply_eq_self] at h₂
  exact eq_sub_of_add_eq h₂.symm
theorem diagMeasure_eq_zero_iff (E : SpectralMeasure Y H) (Δ : BorelSubsets Y) (ψ : H) :
    E.diagMeasure ψ Δ.1 = 0 ↔ E Δ ψ = 0 := by
  rw [E.diagMeasure_apply, ENNReal.ofReal_eq_zero]
  constructor
  · intro h
    have h₀ : ‖E Δ ψ‖ ^ 2 = 0 := le_antisymm h (by positivity)
    simpa using h₀
  · intro h
    simp [h]
theorem integrable_norm_sq_of_mem_integralDom (E : SpectralMeasure Y H) {g : Y → ℂ}
    (hg : Measurable g) {ψ : H} (hψ : ψ ∈ E.integralDom g) :
    Integrable (fun y => ‖g y‖ ^ 2) (E.diagMeasure ψ) := by
  refine ⟨(hg.norm.pow_const 2).aestronglyMeasurable, ?_⟩
  rw [hasFiniteIntegral_iff_enorm]
  have h : ∫⁻ y, ‖g y‖ₑ ^ 2 ∂E.diagMeasure ψ < ∞ := hψ
  simpa [enorm_pow] using h
theorem integralApply_eq_zero_iff (E : SpectralMeasure Y H) (hU : UnboundedFunctionalCalculus E)
    {g : Y → ℂ} (hg : Measurable g) {ψ : H} (hψ : ψ ∈ E.integralDom g) :
    E.integralApply g ψ = 0 ↔ E (nonzeroLocus hg) ψ = 0 := by
  rw [← diagMeasure_eq_zero_iff]
  have h₁ := hU.norm_sq g hg ψ hψ
  have h₂ := integral_eq_zero_iff_of_nonneg (μ := E.diagMeasure ψ)
    (f := fun y => ‖g y‖ ^ 2) (fun y => by positivity)
    (integrable_norm_sq_of_mem_integralDom E hg hψ)
  have h₃ : (fun y => ‖g y‖ ^ 2) =ᵐ[E.diagMeasure ψ] 0 ↔
      E.diagMeasure ψ (nonzeroLocus hg).1 = 0 := by
    rw [Filter.EventuallyEq, ae_iff]
    have hs : {a | ¬ ‖g a‖ ^ 2 = (0 : Y → ℝ) a} = (nonzeroLocus hg).1 := by
      ext y
      simp [nonzeroLocus]
    rw [hs]
  rw [← h₃, ← h₂, ← h₁]
  simp
theorem mem_integralDom_of_apply_eq_zero (E : SpectralMeasure Y H) {g : Y → ℂ}
    (hg : Measurable g) {ψ : H} (h : E (nonzeroLocus hg) ψ = 0) : ψ ∈ E.integralDom g := by
  have h₀ := (diagMeasure_eq_zero_iff E (nonzeroLocus hg) ψ).2 h
  have hae : (fun y => ‖g y‖ₑ ^ 2) =ᵐ[E.diagMeasure ψ] 0 := by
    filter_upwards [compl_mem_ae_iff.mpr h₀] with y hy
    have hy₀ : g y = 0 := by simpa [nonzeroLocus] using hy
    simp [hy₀]
  show ∫⁻ y, ‖g y‖ₑ ^ 2 ∂E.diagMeasure ψ < ∞
  rw [lintegral_congr_ae hae]
  simp
theorem ker_integral_eq_range (E : SpectralMeasure Y H) (hB : BoundedFunctionalCalculus E)
    (hU : UnboundedFunctionalCalculus E) (g : Y → ℂ) (hg : Measurable g) :
    {ψ | ψ ∈ E.integralDom g ∧ E.integralApply g ψ = 0} = Set.range (E (zeroLocus hg)) := by
  have hc : nonzeroLocus hg = ⟨(zeroLocus hg).1ᶜ, (zeroLocus hg).2.compl⟩ := rfl
  ext ψ
  constructor
  · rintro ⟨hψ, hv⟩
    have h₁ := (integralApply_eq_zero_iff E hU hg hψ).1 hv
    rw [hc, apply_compl_apply E hB] at h₁
    exact ⟨ψ, (sub_eq_zero.mp h₁).symm⟩
  · rintro ⟨φ, rfl⟩
    have hi : E (zeroLocus hg) (E (zeroLocus hg) φ) = E (zeroLocus hg) φ :=
      congrArg (fun T : H →L[ℂ] H => T φ) (E.isStarProjection (zeroLocus hg)).isIdempotentElem.eq
    have h₀ : E (nonzeroLocus hg) (E (zeroLocus hg) φ) = 0 := by
      rw [hc, apply_compl_apply E hB, hi, sub_self]
    have hd := mem_integralDom_of_apply_eq_zero E hg h₀
    exact ⟨hd, (integralApply_eq_zero_iff E hU hg hd).2 h₀⟩
theorem integralApply_vanishes_iff (E : SpectralMeasure Y H) (hU : UnboundedFunctionalCalculus E)
    (g : Y → ℂ) (hg : Measurable g) :
    (∀ ψ ∈ E.integralDom g, E.integralApply g ψ = 0) ↔ E (nonzeroLocus hg) = 0 := by
  constructor
  · intro h
    obtain ⟨A, hd, hA⟩ := hU.exists_op g hg
    rw [hA.1] at hd
    have hcl : IsClosed {ψ | E (nonzeroLocus hg) ψ = 0} :=
      isClosed_eq (E (nonzeroLocus hg)).continuous continuous_const
    have hsub : E.integralDom g ⊆ {ψ | E (nonzeroLocus hg) ψ = 0} := fun ψ hψ =>
      (integralApply_eq_zero_iff E hU hg hψ).1 (h ψ hψ)
    have hall := hcl.closure_subset_iff.2 hsub
    rw [hd.closure_eq] at hall
    ext ψ
    simpa using hall (mem_univ ψ)
  · intro h ψ hψ
    exact (integralApply_eq_zero_iff E hU hg hψ).2 (by rw [h]; simp)
theorem integral_eq_ofReal_integral_re_of_isRealValued {μ : Measure Y} {g : Y → ℂ}
    (hr : IsRealValued g) : ∫ y, g y ∂μ = ((∫ y, (g y).re ∂μ : ℝ) : ℂ) := by
  rw [← integral_complex_ofReal]
  refine integral_congr_ae (Eventually.of_forall fun y => ?_)
  apply Complex.ext <;> simp [hr y]
theorem apply_eq_zero_of_inner_nonneg (E : SpectralMeasure Y H) (hB : BoundedFunctionalCalculus E)
    (hU : UnboundedFunctionalCalculus E) {g : Y → ℂ} (hg : Measurable g) (hr : IsRealValued g)
    (hpos : ∀ ψ ∈ E.integralDom g, 0 ≤ ⟪ψ, E.integralApply g ψ⟫_ℂ) (r : ℕ) (D : BorelSubsets Y)
    (hD : ∀ y ∈ D.1, (g y).re ≤ -(1 / ((r : ℝ) + 1)) ∧ ‖g y‖ ≤ r) : E D = 0 := by
  ext φ
  obtain ⟨ψ, hψ⟩ : ∃ ψ, ψ = E D φ := ⟨_, rfl⟩
  have hcar : E.diagMeasure ψ D.1ᶜ = 0 := hB.diagMeasure_compl D ψ ⟨φ, hψ.symm⟩
  have hae : ∀ᵐ y ∂E.diagMeasure ψ, y ∈ D.1 := by
    filter_upwards [compl_mem_ae_iff.mpr hcar] with y hy
    simpa using hy
  have hdom : ψ ∈ E.integralDom g := by
    show ∫⁻ y, ‖g y‖ₑ ^ 2 ∂E.diagMeasure ψ < ∞
    refine (lintegral_mono_ae (g := fun _ => ENNReal.ofReal (r : ℝ) ^ 2) ?_).trans_lt ?_
    · filter_upwards [hae] with y hy
      gcongr
      rw [← ofReal_norm]
      exact ENNReal.ofReal_le_ofReal (hD y hy).2
    · rw [lintegral_const]
      exact ENNReal.mul_lt_top (by simp) (measure_lt_top _ _)
  have hint : Integrable (fun y => (g y).re) (E.diagMeasure ψ) := by
    refine Integrable.of_bound (Complex.measurable_re.comp hg).aestronglyMeasurable (r : ℝ) ?_
    filter_upwards [hae] with y hy
    exact (Complex.abs_re_le_norm _).trans (hD y hy).2
  have hle : ∫ y, (g y).re ∂E.diagMeasure ψ ≤
      ∫ _, -(1 / ((r : ℝ) + 1)) ∂E.diagMeasure ψ := by
    refine integral_mono_ae hint (integrable_const _) ?_
    filter_upwards [hae] with y hy
    exact (hD y hy).1
  have hmass : (E.diagMeasure ψ).real univ = ‖ψ‖ ^ 2 := by
    rw [Measure.real, E.diagMeasure_univ, ENNReal.toReal_ofReal (by positivity)]
  have hconst : ∫ _, -(1 / ((r : ℝ) + 1)) ∂E.diagMeasure ψ =
      -(‖ψ‖ ^ 2 / ((r : ℝ) + 1)) := by
    rw [integral_const, smul_eq_mul, show (E.diagMeasure ψ).real univ = ‖ψ‖ ^ 2 from hmass]
    ring
  have hp := hpos ψ hdom
  rw [hU.inner_eq g hg ψ hdom, integral_eq_ofReal_integral_re_of_isRealValued hr] at hp
  have hp' : 0 ≤ ∫ y, (g y).re ∂E.diagMeasure ψ := Complex.zero_le_real.mp hp
  have hq : ‖ψ‖ ^ 2 / ((r : ℝ) + 1) ≤ 0 := by linarith
  have hq' : ‖ψ‖ ^ 2 ≤ 0 := by
    have hr₀ : (0 : ℝ) < (r : ℝ) + 1 := by positivity
    rwa [div_le_iff₀ hr₀, zero_mul] at hq
  have h₀ : ψ = 0 := by
    have : ‖ψ‖ ^ 2 = 0 := le_antisymm hq' (by positivity)
    simpa using this
  simpa [hψ] using h₀
theorem inner_nonneg_iff_apply_negativeLocus_eq_zero (E : SpectralMeasure Y H)
    (hB : BoundedFunctionalCalculus E) (hU : UnboundedFunctionalCalculus E) (g : Y → ℂ)
    (hg : Measurable g) (hr : IsRealValued g) :
    (∀ ψ ∈ E.integralDom g, 0 ≤ ⟪ψ, E.integralApply g ψ⟫_ℂ) ↔ E (negativeLocus hg) = 0 := by
  constructor
  · intro hpos
    have hre : Measurable fun y => (g y).re := Complex.measurable_re.comp hg
    let D : ℕ → BorelSubsets Y := fun r =>
      ⟨{y | (g y).re ≤ -(1 / ((r : ℝ) + 1))} ∩ {y | ‖g y‖ ≤ r},
        (measurableSet_le hre measurable_const).inter (measurableSet_le hg.norm measurable_const)⟩
    have hz : ∀ r, E (D r) = 0 := fun r =>
      apply_eq_zero_of_inner_nonneg E hB hU hg hr hpos r (D r) fun y hy => hy
    have hu : negativeLocus hg = ⟨⋃ r, (D r).1, MeasurableSet.iUnion fun r => (D r).2⟩ := by
      refine Subtype.ext (Set.ext fun y => ?_)
      constructor
      · intro hy
        have hy' : (g y).re < 0 := hy
        obtain ⟨a, ha⟩ := exists_nat_gt (1 / (-(g y).re))
        obtain ⟨b, hb⟩ := exists_nat_ge ‖g y‖
        have hneg : 0 < -(g y).re := by linarith
        have ha₁ : 1 / (((max a b : ℕ) : ℝ) + 1) ≤ -(g y).re := by
          have hpos₁ : (0 : ℝ) < ((max a b : ℕ) : ℝ) + 1 := by positivity
          rw [div_le_iff₀ hpos₁]
          have h₁ : (a : ℝ) ≤ ((max a b : ℕ) : ℝ) := by exact_mod_cast le_max_left a b
          rw [div_lt_iff₀ hneg] at ha
          nlinarith
        refine mem_iUnion.mpr ⟨max a b, ?_, ?_⟩
        · show (g y).re ≤ _
          linarith
        · show ‖g y‖ ≤ _
          exact hb.trans (by exact_mod_cast le_max_right a b)
      · intro hy
        obtain ⟨r, hr₁, -⟩ := mem_iUnion.mp hy
        have hr₁' : (g y).re ≤ -(1 / ((r : ℝ) + 1)) := hr₁
        have hp : (0 : ℝ) < 1 / ((r : ℝ) + 1) := by positivity
        show (g y).re < 0
        linarith
    rw [hu]
    exact hB.apply_iUnion ℕ D hz
  · intro h ψ hψ
    rw [hU.inner_eq g hg ψ hψ, integral_eq_ofReal_integral_re_of_isRealValued hr]
    have h₀ : E.diagMeasure ψ (negativeLocus hg).1 = 0 :=
      (diagMeasure_eq_zero_iff E _ ψ).2 (by rw [h]; simp)
    have hnn : 0 ≤ ∫ y, (g y).re ∂E.diagMeasure ψ := by
      refine integral_nonneg_of_ae ?_
      filter_upwards [compl_mem_ae_iff.mpr h₀] with y hy
      have hy' : ¬ (g y).re < 0 := hy
      exact not_lt.mp hy'
    exact Complex.zero_le_real.mpr hnn
theorem spectralKernelPositivityTheorem_of_calculi
    (hB : SpectralTheory.BoundedBorelCalculus.BoundedBorelCalculusHolds)
    (hU : UnboundedFunctionalCalculusHolds) : SpectralKernelPositivityTheorem := by
  intro H _ _ _ n Y E
  exact ⟨ker_integral_eq_range E (hB H n Y E) (hU H n Y E),
    integralApply_vanishes_iff E (hU H n Y E),
    inner_nonneg_iff_apply_negativeLocus_eq_zero E (hB H n Y E) (hU H n Y E)⟩
end YangMills.Construction.SpectralKernel
