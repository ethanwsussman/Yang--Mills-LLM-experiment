import YangMills.Construction.InfiniteLattice.ConditionalExpectationGivenTheInvariantField
import YangMills.Construction.InfiniteLattice.InvariantFunctionsLongRangeOrderAndErgodicMeasures
import YangMills.Construction.InfiniteLattice.TopologyAndDensityOnTheConfigurationsOfOneLattice
import YangMills.Construction.InfiniteLattice.VanishingLongRangeOrderOnADenseSetGivesErgodicity
import Mathlib
set_option autoImplicit false
open MeasureTheory YangMills.Construction.InfiniteLattice
noncomputable section
namespace YangMills.Construction.LatticePhases.ShiftErgodicityCriterion
theorem shiftInvariantSigma_le (a : ℝ) :
    shiftInvariantSigma a ≤ (inferInstance : MeasurableSpace (GaugeField a)) :=
  fun _ hs => hs.1
theorem integral_mul_eq_mul_of_plateauVariance_eq_zero
    (hcond : CondExpInvariant.Claim)
    (hinv : InvariantFunctionsAndErgodicity)
    (D : Setup) (μ : ProbMeasure (GaugeField D.mesh)) (hμ : IsShiftInvariant μ.toMeasure)
    {f : GaugeField D.mesh → ℂ} (hf : IsBoundedObservable f)
    (hpv : plateauVariance μ.toMeasure f = 0)
    {g : GaugeField D.mesh → ℂ} (hg : Measurable[shiftInvariantSigma D.mesh] g)
    (hgb : ∃ C : ℝ, ∀ U, ‖g U‖ ≤ C) :
    ∫ U, g U * f U ∂μ.toMeasure = (∫ U, f U ∂μ.toMeasure) * ∫ U, g U ∂μ.toMeasure := by
  obtain ⟨⟨-, -, -, -, ⟨Y, hY, hYb⟩, -⟩, -, hmean, -, -⟩ := hcond D μ.toMeasure hμ f f hf hf
  have hvar : varianceOf μ.toMeasure Y = 0 := by
    have h := ((hinv D).2.1 μ hμ f hf Y hY).1
    rw [hpv] at h
    exact_mod_cast h.symm
  have hYm : Measurable Y := hY.1.mono (shiftInvariantSigma_le D.mesh) le_rfl
  set c : ℂ := ∫ V, Y V ∂μ.toMeasure with hc
  have hsq : Integrable (fun U => ‖Y U - c‖ ^ 2) μ.toMeasure := by
    refine Integrable.of_bound (C := (observableSupNorm f + ‖c‖) ^ 2)
      (((hYm.sub_const c).norm.pow_const 2).aestronglyMeasurable) ?_
    refine Filter.Eventually.of_forall fun U => ?_
    have h1 : ‖Y U - c‖ ≤ observableSupNorm f + ‖c‖ :=
      (norm_sub_le _ _).trans (by linarith [hYb U])
    rw [Real.norm_of_nonneg (by positivity)]
    exact pow_le_pow_left₀ (norm_nonneg _) h1 2
  have hae : ∀ᵐ U ∂μ.toMeasure, Y U = c := by
    have h0 := (integral_eq_zero_iff_of_nonneg (fun U => by positivity) hsq).mp hvar
    filter_upwards [h0] with U hU
    have hU' : ‖Y U - c‖ ^ 2 = 0 := hU
    exact sub_eq_zero.mp (norm_eq_zero.mp (pow_eq_zero_iff (two_ne_zero) |>.mp hU'))
  have hmeanf : c = ∫ U, f U ∂μ.toMeasure := (hmean Y hY).1
  rw [← hY.2.2 g hg hgb, ← hmeanf]
  have hswap : ∫ U, g U * Y U ∂μ.toMeasure = ∫ U, c * g U ∂μ.toMeasure := by
    refine integral_congr_ae ?_
    filter_upwards [hae] with U hU
    rw [hU, mul_comm]
  rw [hswap, integral_const_mul]
theorem exists_mem_integral_norm_sub_lt_of_dense {D : Setup} (T : TopologyDensity D)
    (μ : ProbMeasure (GaugeField D.mesh)) {S : Set C(GaugeField D.mesh, ℂ)}
    (hS : ∀ F : C(GaugeField D.mesh, ℂ), ∀ ε : ℝ, 0 < ε →
      ∃ f ∈ S, uniformSup (fun U => F U - f U) < ε)
    {g : GaugeField D.mesh → ℂ} (hg : Integrable g μ.toMeasure) {ε : ℝ} (hε : 0 < ε) :
    ∃ f ∈ S, ∫ U, ‖g U - f U‖ ∂μ.toMeasure < ε := by
  have := T.compact
  obtain ⟨Z, ⟨F, hF⟩, hd⟩ :=
    (T.dense_Lp1 μ).exists_dist_lt (hg.toL1 g : μ.Lp1) (half_pos hε)
  obtain ⟨f, hfS, hsup⟩ := hS F (ε / 2) (half_pos hε)
  refine ⟨f, hfS, ?_⟩
  have hnorm : ‖(hg.toL1 g : μ.Lp1) - Z‖ = ∫ U, ‖g U - F U‖ ∂μ.toMeasure := by
    rw [L1.norm_eq_integral_norm]
    refine integral_congr_ae ?_
    filter_upwards [Lp.coeFn_sub (hg.toL1 g : μ.Lp1) Z, hg.coeFn_toL1, hF] with U h1 h2 h3
    rw [h1, Pi.sub_apply, h2, h3]
  rw [dist_eq_norm, hnorm] at hd
  have hbdd : BddAbove (Set.range fun U => ‖F U - f U‖) :=
    (isCompact_range ((F - f).continuous.norm)).bddAbove
  have hpt : ∀ U, ‖F U - f U‖ ≤ ε / 2 := fun U =>
    ((le_ciSup hbdd U).trans_eq rfl).trans hsup.le
  have hFi : Integrable (F : GaugeField D.mesh → ℂ) μ.toMeasure :=
    Integrable.of_bound F.continuous.measurable.aestronglyMeasurable _
      (Filter.Eventually.of_forall fun U =>
        le_ciSup (isCompact_range F.continuous.norm).bddAbove U)
  have hfi : Integrable (f : GaugeField D.mesh → ℂ) μ.toMeasure :=
    Integrable.of_bound f.continuous.measurable.aestronglyMeasurable _
      (Filter.Eventually.of_forall fun U =>
        le_ciSup (isCompact_range f.continuous.norm).bddAbove U)
  have hle : ∫ U, ‖g U - f U‖ ∂μ.toMeasure ≤ ∫ U, ‖g U - F U‖ + ε / 2 ∂μ.toMeasure := by
    refine integral_mono (hg.sub hfi).norm (((hg.sub hFi).norm).add (integrable_const _)) ?_
    intro U
    calc ‖g U - f U‖ = ‖(g U - F U) + (F U - f U)‖ := by rw [sub_add_sub_cancel]
      _ ≤ ‖g U - F U‖ + ‖F U - f U‖ := norm_add_le _ _
      _ ≤ ‖g U - F U‖ + ε / 2 := by linarith [hpt U]
  have hsplit : ∫ U, ‖g U - F U‖ + ε / 2 ∂μ.toMeasure =
      ∫ U, ‖g U - F U‖ ∂μ.toMeasure + ε / 2 := by
    rw [integral_add (f := fun U => ‖g U - F U‖) (g := fun _ => ε / 2) (hg.sub hFi).norm
      (integrable_const _), integral_const]
    simp
  linarith
theorem statement_holds
    (hcond : CondExpInvariant.Claim)
    (hinv : InvariantFunctionsAndErgodicity)
    (htop : TopologyDensityHolds) : Statement := by
  intro D μ S hμ hS hpv
  refine ⟨inferInstance, hμ, fun I hI => ?_⟩
  have T := htop D
  have := T.compact
  have hIm : MeasurableSet I := hI.1
  set g : GaugeField D.mesh → ℂ := I.indicator 1 with hgdef
  have hgm : Measurable[shiftInvariantSigma D.mesh] g := by
    show Measurable[shiftInvariantSigma D.mesh] (I.indicator fun _ => (1 : ℂ))
    exact measurable_const.indicator hI
  have hgb : ∀ U, ‖g U‖ ≤ 1 := fun U => by
    by_cases h : U ∈ I <;> simp [hgdef, h]
  have hgi : Integrable g μ.toMeasure :=
    Integrable.of_bound (hgm.mono (shiftInvariantSigma_le D.mesh) le_rfl).aestronglyMeasurable 1
      (Filter.Eventually.of_forall hgb)
  set p : ℝ := μ.toMeasure.real I with hpdef
  have hp0 : 0 ≤ p := measureReal_nonneg
  have hp1 : p ≤ 1 := measureReal_le_one
  have hgint : ∫ U, g U ∂μ.toMeasure = (p : ℂ) := by
    rw [hgdef, integral_indicator hIm]
    simp [hpdef]
  have hgg : ∀ U, g U * g U = g U := fun U => by
    by_cases h : U ∈ I <;> simp [hgdef, h]
  have hsmall : ∀ ε : ℝ, 0 < ε → ‖(p : ℂ) - (p : ℂ) * p‖ ≤ 2 * ε := by
    intro ε hε
    obtain ⟨f, hfS, hclose⟩ := exists_mem_integral_norm_sub_lt_of_dense T μ hS hgi hε
    have hfc : Continuous (f : GaugeField D.mesh → ℂ) := f.continuous
    have hfb : ∃ C : ℝ, ∀ U, ‖f U‖ ≤ C :=
      ⟨_, fun U => le_ciSup (isCompact_range hfc.norm).bddAbove U⟩
    have hobs : IsBoundedObservable (fun U => f U) := ⟨hfc.measurable, hfb⟩
    have hfi : Integrable (fun U => f U) μ.toMeasure :=
      Integrable.of_bound hfc.measurable.aestronglyMeasurable _
        (Filter.Eventually.of_forall hfb.choose_spec)
    have hprod := integral_mul_eq_mul_of_plateauVariance_eq_zero hcond hinv D μ hμ hobs
      (hpv f hfS) hgm ⟨1, hgb⟩
    rw [hgint] at hprod
    have hgfi : Integrable (fun U => g U * f U) μ.toMeasure :=
      hfi.bdd_mul (hgm.mono (shiftInvariantSigma_le D.mesh) le_rfl).aestronglyMeasurable
        (Filter.Eventually.of_forall hgb)
    have h1 : ‖(p : ℂ) - ∫ U, f U ∂μ.toMeasure‖ ≤ ε := by
      rw [← hgint, ← integral_sub hgi hfi]
      exact (norm_integral_le_integral_norm _).trans hclose.le
    have h2 : ‖(p : ℂ) - ∫ U, g U * f U ∂μ.toMeasure‖ ≤ ε := by
      have he : (p : ℂ) - ∫ U, g U * f U ∂μ.toMeasure =
          ∫ U, g U * (g U - f U) ∂μ.toMeasure := by
        rw [← hgint, ← integral_sub hgi hgfi]
        refine integral_congr_ae (Filter.Eventually.of_forall fun U => ?_)
        show g U - g U * f U = g U * (g U - f U)
        rw [mul_sub, hgg]
      rw [he]
      refine (norm_integral_le_integral_norm _).trans (le_trans ?_ hclose.le)
      refine integral_mono_of_nonneg (Filter.Eventually.of_forall fun U => norm_nonneg _)
        (hgi.sub hfi).norm (Filter.Eventually.of_forall fun U => ?_)
      show ‖g U * (g U - f U)‖ ≤ ‖g U - f U‖
      rw [norm_mul]
      exact mul_le_of_le_one_left (norm_nonneg _) (hgb U)
    have hpn : ‖(p : ℂ)‖ ≤ 1 := by
      rw [Complex.norm_real, Real.norm_of_nonneg hp0]
      exact hp1
    have h3 : ‖(∫ U, f U ∂μ.toMeasure) * (p : ℂ) - (p : ℂ) * p‖ ≤ ε := by
      have hre : (∫ U, f U ∂μ.toMeasure) * (p : ℂ) - (p : ℂ) * p =
          -(((p : ℂ) - ∫ U, f U ∂μ.toMeasure) * (p : ℂ)) := by ring
      rw [hre, norm_neg, norm_mul]
      calc _ ≤ ε * 1 := mul_le_mul h1 hpn (norm_nonneg _) hε.le
        _ = ε := mul_one ε
    calc ‖(p : ℂ) - (p : ℂ) * p‖
        = ‖((p : ℂ) - ∫ U, g U * f U ∂μ.toMeasure) +
            ((∫ U, f U ∂μ.toMeasure) * (p : ℂ) - (p : ℂ) * p)‖ := by
          rw [hprod]; congr 1; ring
      _ ≤ 2 * ε := (norm_add_le _ _).trans (by linarith)
  have hzero : (p : ℂ) - (p : ℂ) * p = 0 := by
    refine norm_le_zero_iff.mp (le_of_forall_pos_le_add fun ε hε => ?_)
    have := hsmall (ε / 2) (half_pos hε)
    linarith
  have hreal : p * (1 - p) = 0 := by
    have hc : ((p * (1 - p) : ℝ) : ℂ) = 0 := by
      push_cast
      linear_combination hzero
    exact_mod_cast hc
  rcases mul_eq_zero.mp hreal with h | h
  · left
    exact (measureReal_eq_zero_iff (measure_ne_top _ _)).mp h
  · right
    have h1 : μ.toMeasure.real I = 1 := by linarith
    rw [Measure.real, ENNReal.toReal_eq_one_iff] at h1
    exact h1
end YangMills.Construction.LatticePhases.ShiftErgodicityCriterion
end
