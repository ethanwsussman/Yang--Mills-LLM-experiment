import YangMills.Construction.LawByMomentsOfTheFlow.LimitFieldsExist
import Mathlib
set_option autoImplicit false
noncomputable section
open MeasureTheory Filter
open scoped Topology ENNReal NNReal
namespace YangMills.Construction.MomentMethod
section
variable (T : TranslatedLaws) {J : Type} [Countable J] (X : J → T.Family)
private def jointValues (i : ℕ) (ω : T.Ω i) : TranslateValues J := fun a => TranslatedLaws.translate (X a.1) a.2 i ω
variable {T X}
private theorem aemeasurable_translate (hT : T.IsPreserving) {Y : T.Family} (hY : TranslatedLaws.HasBoundedMoments Y) (k i : ℕ) :
    AEMeasurable (TranslatedLaws.translate Y k i) (T.μ i) :=
  (hY.aemeasurable i).comp_quasiMeasurePreserving ((hT.measurePreserving i).iterate k).quasiMeasurePreserving
private theorem aemeasurable_jointValues (hT : T.IsPreserving) (hX : ∀ j, TranslatedLaws.HasBoundedMoments (X j)) (i : ℕ) :
    AEMeasurable (jointValues T X i) (T.μ i) :=
  aemeasurable_pi_lambda _ fun a => aemeasurable_translate hT (hX a.1) a.2 i
private theorem lintegral_sq_translate (hT : T.IsPreserving) {Y : T.Family} (hY : TranslatedLaws.HasBoundedMoments Y) (k i : ℕ) :
    ∫⁻ ω, ENNReal.ofReal (|TranslatedLaws.translate Y k i ω| ^ 2) ∂(T.μ i) = ∫⁻ ω, ENNReal.ofReal (|Y i ω| ^ 2) ∂(T.μ i) := by
  have hpres := (hT.measurePreserving i).iterate k
  have hmeas : AEMeasurable (fun ω => ENNReal.ofReal (|Y i ω| ^ 2)) (T.μ i) :=
    ENNReal.measurable_ofReal.comp_aemeasurable ((continuous_abs.measurable.comp_aemeasurable (hY.aemeasurable i)).pow_const 2)
  have := lintegral_map' (μ := T.μ i) (f := fun ω => ENNReal.ofReal (|Y i ω| ^ 2)) (g := (T.τ i)^[k])
    (by rw [hpres.map_eq]; exact hmeas) hpres.measurable.aemeasurable
  rw [hpres.map_eq] at this
  exact this.symm
private theorem measure_abs_translate_gt_le (hT : T.IsPreserving) {Y : T.Family} (hY : TranslatedLaws.HasBoundedMoments Y) (k i : ℕ) {C r : ℝ} (hr : 0 < r)
    (hC : ∫⁻ ω, ENNReal.ofReal (|Y i ω| ^ 2) ∂(T.μ i) ≤ ENNReal.ofReal C) :
    T.μ i {ω | r < |TranslatedLaws.translate Y k i ω|} ≤ ENNReal.ofReal C / ENNReal.ofReal (r ^ 2) := by
  have hmeas : AEMeasurable (fun ω => ENNReal.ofReal (|TranslatedLaws.translate Y k i ω| ^ 2)) (T.μ i) :=
    ENNReal.measurable_ofReal.comp_aemeasurable
      ((continuous_abs.measurable.comp_aemeasurable (aemeasurable_translate hT hY k i)).pow_const 2)
  have hne : ENNReal.ofReal (r ^ 2) ≠ 0 := by
    rw [Ne, ENNReal.ofReal_eq_zero, not_le]
    positivity
  have hmarkov := meas_ge_le_lintegral_div hmeas hne ENNReal.ofReal_ne_top
  refine (measure_mono fun ω hω => ?_).trans (hmarkov.trans ?_)
  · have hω' : r < |TranslatedLaws.translate Y k i ω| := hω
    refine ENNReal.ofReal_le_ofReal ?_
    exact pow_le_pow_left₀ hr.le hω'.le 2
  · rw [lintegral_sq_translate hT hY k i]
    exact ENNReal.div_le_div_right hC _
end
theorem exists_jointLimitLaw : exists_jointLimitLaw_statement := by
  intro T J _ X hT hX
  haveI := hT.isProbability
  let law : ℕ → ProbabilityMeasure (TranslateValues J) := fun i =>
    ⟨(T.μ i).map (jointValues T X i), Measure.isProbabilityMeasure_map (aemeasurable_jointValues hT hX i)⟩
  have tight : IsTightMeasureSet {((m : ProbabilityMeasure (TranslateValues J)) : Measure (TranslateValues J)) | m ∈ Set.range law} := by
    rw [isTightMeasureSet_iff_exists_isCompact_measure_compl_le]
    intro ε hε
    obtain ⟨e, he⟩ := exists_injective_nat (J × ℕ)
    choose Ca hCa using fun a : J × ℕ => (hX a.1).moment_bound 2
    obtain ⟨ε', hε'⟩ : ∃ ε', ε' = min ε 1 := ⟨_, rfl⟩
    have hε'0 : ε' ≠ 0 := by
      rw [hε']
      exact (lt_min hε one_pos).ne'
    have hε't : ε' ≠ ∞ := by
      rw [hε']
      exact (lt_of_le_of_lt (min_le_right _ _) ENNReal.one_lt_top).ne
    obtain ⟨w, hw⟩ : ∃ w : J × ℕ → ℝ≥0∞, ∀ a, w a = ε' * (2⁻¹ : ℝ≥0∞) ^ e a * 2⁻¹ := ⟨_, fun _ => rfl⟩
    have hw0 : ∀ a, w a ≠ 0 := fun a => by
      rw [hw]
      simp [hε'0, ENNReal.pow_eq_top_iff]
    have hwt : ∀ a, w a ≠ ∞ := fun a => by
      rw [hw]
      refine ENNReal.mul_ne_top (ENNReal.mul_ne_top hε't (ENNReal.pow_ne_top (by simp))) (by simp)
    have hsum : ∑' a, w a ≤ ε := by
      have h1 : ∑' a, (2⁻¹ : ℝ≥0∞) ^ e a ≤ ∑' n : ℕ, (2⁻¹ : ℝ≥0∞) ^ n :=
        ENNReal.tsum_comp_le_tsum_of_injective he fun n => (2⁻¹ : ℝ≥0∞) ^ n
      have h2 : ∑' n : ℕ, (2⁻¹ : ℝ≥0∞) ^ n = 2 := by
        rw [ENNReal.tsum_geometric, ENNReal.one_sub_inv_two, inv_inv]
      calc ∑' a, w a = ε' * (∑' a, (2⁻¹ : ℝ≥0∞) ^ e a) * 2⁻¹ := by
            simp_rw [hw]
            rw [ENNReal.tsum_mul_right, ENNReal.tsum_mul_left]
        _ ≤ ε' * 2 * 2⁻¹ := by
            gcongr
            exact h1.trans h2.le
        _ = ε' := by
            rw [mul_assoc, ENNReal.mul_inv_cancel (by simp) (by simp), mul_one]
        _ ≤ ε := by
            rw [hε']
            exact min_le_left _ _
    obtain ⟨R, hR⟩ : ∃ R : J × ℕ → ℝ, ∀ a, R a = Real.sqrt ((|Ca a| + 1) / (w a).toReal) := ⟨_, fun _ => rfl⟩
    have hwr : ∀ a, 0 < (w a).toReal := fun a => ENNReal.toReal_pos (hw0 a) (hwt a)
    have hR0 : ∀ a, 0 < R a := fun a => by
      rw [hR]
      exact Real.sqrt_pos.mpr (div_pos (by positivity) (hwr a))
    have hR2 : ∀ a, R a ^ 2 = (|Ca a| + 1) / (w a).toReal := fun a => by
      rw [hR, Real.sq_sqrt (div_nonneg (by positivity) (hwr a).le)]
    refine ⟨Set.univ.pi fun a => Set.Icc (-R a) (R a), isCompact_univ_pi fun _ => isCompact_Icc, ?_⟩
    rintro _ ⟨m, ⟨i, rfl⟩, rfl⟩
    have hclosed : MeasurableSet (Set.univ.pi fun a => Set.Icc (-R a) (R a) : Set (TranslateValues J))ᶜ :=
      (MeasurableSet.univ_pi fun _ => measurableSet_Icc).compl
    show ((T.μ i).map (jointValues T X i)) _ ≤ ε
    rw [Measure.map_apply_of_aemeasurable (aemeasurable_jointValues hT hX i) hclosed]
    have hsub : jointValues T X i ⁻¹' (Set.univ.pi fun a => Set.Icc (-R a) (R a) : Set (TranslateValues J))ᶜ ⊆
        ⋃ a : J × ℕ, {ω | R a < |TranslatedLaws.translate (X a.1) a.2 i ω|} := by
      intro ω hω
      simp only [Set.mem_preimage, Set.mem_compl_iff, Set.mem_pi, Set.mem_univ, true_imp_iff, not_forall] at hω
      obtain ⟨a, ha⟩ := hω
      refine Set.mem_iUnion.mpr ⟨a, ?_⟩
      by_contra hle
      exact ha (abs_le.mp (not_lt.mp hle))
    refine (measure_mono hsub).trans ((measure_iUnion_le _).trans (le_trans (ENNReal.tsum_le_tsum fun a => ?_) hsum))
    refine (measure_abs_translate_gt_le hT (hX a.1) a.2 i (hR0 a) (hCa a i)).trans ?_
    refine ENNReal.div_le_of_le_mul ?_
    have h3 : w a * ENNReal.ofReal (R a ^ 2) = ENNReal.ofReal (|Ca a| + 1) := by
      rw [hR2, ← ENNReal.ofReal_toReal (hwt a), ← ENNReal.ofReal_mul (hwr a).le, ENNReal.toReal_ofReal (hwr a).le]
      congr 1
      field_simp [(hwr a).ne']
    rw [h3]
    exact ENNReal.ofReal_le_ofReal (by linarith [le_abs_self (Ca a)])
  have hcomp := isCompact_closure_of_isTightMeasureSet tight
  obtain ⟨Q, -, sub, hsub, hlim⟩ := hcomp.isSeqCompact fun n => subset_closure (Set.mem_range_self n)
  refine ⟨sub, (Q : Measure (TranslateValues J)), hsub, inferInstance, ?_⟩
  intro l a G hG ⟨C, hC⟩
  have hcont : Continuous fun v : TranslateValues J => G fun c => v (a c) :=
    hG.comp (continuous_pi fun c => continuous_apply (a c))
  let f : BoundedContinuousFunction (TranslateValues J) ℝ :=
    BoundedContinuousFunction.ofNormedAddCommGroup (fun v => G fun c => v (a c)) hcont C (fun v => by
      rw [Real.norm_eq_abs]
      exact hC _)
  have h1 := (ProbabilityMeasure.tendsto_iff_forall_integral_tendsto.mp hlim) f
  refine h1.congr fun i => ?_
  show ∫ v, G (fun c => v (a c)) ∂((T.μ (sub i)).map (jointValues T X (sub i))) = _
  rw [integral_map (aemeasurable_jointValues hT hX (sub i)) hcont.aestronglyMeasurable]
  rfl
end YangMills.Construction.MomentMethod
end
