import YangMills.Construction.SpectralMeasures.ComplexMeasureUnseenByContinuousFunctions
import Mathlib
set_option autoImplicit false
open MeasureTheory Filter Topology
open scoped NNReal ENNReal
noncomputable section
namespace YangMills.Construction.ComplexMeasureVanishing
open YangMills.Construction.RotationNotation
section ProperSpaces
variable {Ω : Type} [MeasurableSpace Ω]
theorem isFiniteMeasure_variation (μ : ComplexMeasure Ω) : IsFiniteMeasure μ.variation := by
  have hle : μ.variation ≤
      (ComplexMeasure.re μ).totalVariation + (ComplexMeasure.im μ).totalVariation := by
    refine VectorMeasure.variation_le_of_forall_enorm_le fun s hs => ?_
    have hsplit : ‖μ s‖ₑ ≤ ‖(μ s).re‖ₑ + ‖(μ s).im‖ₑ := by
      rw [← ofReal_norm, ← ofReal_norm, ← ofReal_norm,
        ← ENNReal.ofReal_add (norm_nonneg _) (norm_nonneg _)]
      exact ENNReal.ofReal_le_ofReal (Complex.norm_le_abs_re_add_abs_im _)
    have hre : ‖(μ s).re‖ₑ ≤ (ComplexMeasure.re μ).totalVariation s := by
      rw [SignedMeasure.totalVariation_eq_variation]
      exact VectorMeasure.enorm_measure_le_variation (ComplexMeasure.re μ) s
    have him : ‖(μ s).im‖ₑ ≤ (ComplexMeasure.im μ).totalVariation s := by
      rw [SignedMeasure.totalVariation_eq_variation]
      exact VectorMeasure.enorm_measure_le_variation (ComplexMeasure.im μ) s
    exact hsplit.trans (add_le_add hre him)
  exact isFiniteMeasure_of_le _ hle
variable [MetricSpace Ω] [ProperSpace Ω] [BorelSpace Ω]
theorem apply_eq_zero_of_isCompact (μ : ComplexMeasure Ω)
    (hμ : ∀ g : Ω → ℝ, Continuous g → HasCompactSupport g →
      integralC μ (fun x => (g x : ℂ)) = 0)
    {K : Set Ω} (hK : IsCompact K) : μ K = 0 := by
  have hfin := isFiniteMeasure_variation μ
  have hKc : IsClosed K := hK.isClosed
  let r : ℕ → ℝ := fun n => 1 / ((n : ℝ) + 1)
  have hr : ∀ n, 0 < r n := fun n => by positivity
  have hr0 : Tendsto r atTop (𝓝 0) := tendsto_one_div_add_atTop_nhds_zero_nat
  let g : ℕ → Ω → ℝ := fun n x => ((thickenedIndicator (hr n) K x : ℝ≥0) : ℝ)
  have hgc : ∀ n, Continuous (g n) := fun n =>
    NNReal.continuous_coe.comp (thickenedIndicator (hr n) K).continuous
  have hgs : ∀ n, HasCompactSupport (g n) := fun n => by
    refine HasCompactSupport.intro (hK.cthickening (r := r n)) fun x hx => ?_
    have hnot : x ∉ Metric.thickening (r n) K :=
      fun hin => hx (Metric.thickening_subset_cthickening _ _ hin)
    change ((thickenedIndicator (hr n) K x : ℝ≥0) : ℝ) = 0
    rw [thickenedIndicator_zero (hr n) K hnot, NNReal.coe_zero]
  have hlim : ∀ x, Tendsto (fun n => ((g n x : ℝ) : ℂ)) atTop
      (𝓝 (K.indicator (fun _ => (1 : ℂ)) x)) := fun x => by
    have t0 := tendsto_pi_nhds.1 (thickenedIndicator_tendsto_indicator_closure hr hr0 K) x
    rw [hKc.closure_eq] at t0
    have t1 := ((Complex.continuous_ofReal.comp NNReal.continuous_coe).tendsto _).comp t0
    have hval : ((fun t : ℝ≥0 => ((t : ℝ) : ℂ)) (K.indicator (fun _ => (1 : ℝ≥0)) x)) =
        K.indicator (fun _ => (1 : ℂ)) x := by
      by_cases hx : x ∈ K <;> simp [hx]
    simpa only [Function.comp_def, hval] using t1
  have hdom : ∀ n x, ‖((g n x : ℝ) : ℂ)‖ ≤ 1 := fun n x => by
    have hle : g n x ≤ 1 := by
      exact_mod_cast thickenedIndicator_le_one (hr n) K x
    have hge : 0 ≤ g n x := NNReal.coe_nonneg _
    rw [Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg hge]
    exact hle
  have hconv : Tendsto (fun n => μ.integral (fun x => ((g n x : ℝ) : ℂ))
      (ContinuousLinearMap.mul ℝ ℂ)) atTop
      (𝓝 (μ.integral (fun x => K.indicator (fun _ => (1 : ℂ)) x)
        (ContinuousLinearMap.mul ℝ ℂ))) :=
    VectorMeasure.tendsto_integral_of_dominated_convergence (fun _ => (1 : ℝ))
    (fun n => (Complex.continuous_ofReal.comp (hgc n)).aestronglyMeasurable)
    (integrable_const _) (fun n => Eventually.of_forall (hdom n))
    (Eventually.of_forall hlim)
  have hvan : (fun n => μ.integral (fun x => ((g n x : ℝ) : ℂ))
      (ContinuousLinearMap.mul ℝ ℂ)) = fun _ => 0 :=
    funext fun n => hμ (g n) (hgc n) (hgs n)
  rw [hvan, VectorMeasure.integral_indicator_const (1 : ℂ) hK.measurableSet] at hconv
  have := tendsto_nhds_unique hconv tendsto_const_nhds
  simpa using this
theorem apply_eq_zero_of_isClosed (μ : ComplexMeasure Ω)
    (hμ : ∀ g : Ω → ℝ, Continuous g → HasCompactSupport g →
      integralC μ (fun x => (g x : ℂ)) = 0)
    {C : Set Ω} (hC : IsClosed C) : μ C = 0 := by
  have hlim := VectorMeasure.tendsto_vectorMeasure_iUnion_atTop_nat (v := μ)
    (s := fun n => C ∩ compactCovering Ω n)
    (fun i j hij => Set.inter_subset_inter_right _ (compactCovering_subset Ω hij))
    (fun n => hC.measurableSet.inter (isCompact_compactCovering Ω n).measurableSet)
  have hunion : ⋃ n, C ∩ compactCovering Ω n = C := by
    rw [← Set.inter_iUnion, iUnion_compactCovering, Set.inter_univ]
  rw [hunion] at hlim
  have hvan : (fun n => μ (C ∩ compactCovering Ω n)) = fun _ => 0 :=
    funext fun n => apply_eq_zero_of_isCompact μ hμ ((isCompact_compactCovering Ω n).inter_left hC)
  rw [hvan] at hlim
  exact tendsto_nhds_unique hlim tendsto_const_nhds
theorem eq_zero_of_properSpace (μ : ComplexMeasure Ω)
    (hμ : ∀ g : Ω → ℝ, Continuous g → HasCompactSupport g →
      integralC μ (fun x => (g x : ℂ)) = 0) : μ = 0 := by
  refine VectorMeasure.ext_of_generateFrom {s | IsClosed s}
    (fun s hs => by simpa using apply_eq_zero_of_isClosed μ hμ hs) ?_ isPiSystem_isClosed
    (by simpa using apply_eq_zero_of_isClosed μ hμ isClosed_univ)
  exact BorelSpace.measurable_eq.trans borel_eq_generateFrom_isClosed
end ProperSpaces
theorem statement_holds : Statement := by
  intro Y μ hμ
  cases Y
  · exact eq_zero_of_properSpace (Ω := ℝ) μ hμ
  · exact eq_zero_of_properSpace (Ω := ℝ × ℝ) μ hμ
  · exact eq_zero_of_properSpace (Ω := Point3) μ hμ
  · exact eq_zero_of_properSpace (Ω := ℝ × Point3) μ hμ
end YangMills.Construction.ComplexMeasureVanishing
end
