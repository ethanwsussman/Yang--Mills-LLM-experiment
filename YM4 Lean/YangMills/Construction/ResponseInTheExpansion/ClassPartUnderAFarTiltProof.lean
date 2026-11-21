import YangMills.Construction.FreeEnergiesOfTheFlow.MeansGivenAStateReadTheCasesProof
import YangMills.Construction.ResponseInTheExpansion.RemainderOfTheResponseReturnsProof
import YangMills.Construction.ClusterExpansionOfAStep.ColumnsOfTheGasProof
import YangMills.Construction.ClusterExpansionOfAStep.ComparisonOfHeldGasesProof
import YangMills.Construction.ResponseInTheExpansion.ClassPartUnderAFarTilt
import YangMills.Construction.ResponseInTheExpansion.FarVariableUnderATiltProof
import YangMills.Construction.ResponseInTheExpansion.InfluenceOfAFarTilt
import Mathlib
set_option autoImplicit false
noncomputable section
open MeasureTheory ProbabilityTheory
open scoped ENNReal
namespace YangMills.Construction
open Dobrushin StepGas StepSettings TorusFields TorusLumps RenormalizationStepParameters CoreColumns WeightedResponses FreeEnergies BlockAverages
namespace ResponseInTheExpansion
namespace FarTiltClassPart
set_option linter.unusedSectionVars false
section Analysis
section Truncation
def truncateAt (M t : ℝ) : ℝ := max (-M) (min M t)
theorem abs_truncateAt_le {M : ℝ} (hM : 0 ≤ M) (t : ℝ) : |truncateAt M t| ≤ M := by apply _root_.YangMills.Construction.ResponseInTheExpansion.RemainderBounds.abs_clamp_le <;> assumption
theorem truncateAt_zero {M : ℝ} (hM : 0 ≤ M) : truncateAt M 0 = 0 := by
  unfold truncateAt
  rw [min_eq_right hM, max_eq_right (by linarith)]
theorem abs_truncateAt_sub_le {M : ℝ} (hM : 0 ≤ M) (t t' : ℝ) : |truncateAt M t - truncateAt M t'| ≤ |t - t'| := by
  have a1 := le_abs_self (t - t')
  have a2 := neg_abs_le (t - t')
  simp only [truncateAt, max_def, min_def]
  split_ifs <;> rw [abs_le] <;> constructor <;> linarith
theorem abs_truncateAt_le_abs {M : ℝ} (hM : 0 ≤ M) (t : ℝ) : |truncateAt M t| ≤ |t| := by
  have := abs_truncateAt_sub_le hM t 0
  rwa [truncateAt_zero hM, sub_zero, sub_zero] at this
theorem abs_sub_truncateAt_le {M c t : ℝ} (hM : 0 ≤ M) (hc : 0 ≤ c) (h : |t| - M ≤ c) : |t - truncateAt M t| ≤ c := by
  have a1 := le_abs_self t
  have a2 := neg_abs_le t
  simp only [truncateAt, max_def, min_def]
  split_ifs <;> rw [abs_le] <;> constructor <;> linarith
theorem truncateAt_eq_self {M t : ℝ} (h : |t| ≤ M) : truncateAt M t = t := by apply _root_.YangMills.DeltaSharedProofs.p15858 <;> assumption
theorem measurable_truncateAt (M : ℝ) : Measurable (truncateAt M) :=
  measurable_const.max (measurable_const.min measurable_id)
end Truncation
section General
variable {α : Type*} [MeasurableSpace α]
theorem integral_sub_le_of_measureReal_le (P P' : Measure α) [IsProbabilityMeasure P] [IsProbabilityMeasure P'] {ε k : ℝ} (hk : 0 ≤ k)
    (hB : ∀ B, MeasurableSet B → P.real B ≤ P'.real B + ε) {g : α → ℝ} (hg : Measurable g) (hb : ∀ s, |g s| ≤ k) :
    ∫ s, g s ∂P - ∫ s, g s ∂P' ≤ 2 * k * ε := by
  set f : α → ℝ := fun s => g s + k with hf
  have hf0 : ∀ s, 0 ≤ f s := fun s => by
    have := (abs_le.mp (hb s)).1
    simp only [hf]
    linarith
  have hf2 : ∀ s, f s ≤ 2 * k := fun s => by
    have := (abs_le.mp (hb s)).2
    simp only [hf]
    linarith
  have hfm : Measurable f := hg.add measurable_const
  have hint : ∀ (Q : Measure α) [IsProbabilityMeasure Q], Integrable f Q := fun Q _ =>
    Integrable.of_bound hfm.aestronglyMeasurable (2 * k) (Filter.Eventually.of_forall fun s => by
      rw [Real.norm_eq_abs, abs_of_nonneg (hf0 s)]
      exact hf2 s)
  have hgint : ∀ (Q : Measure α) [IsProbabilityMeasure Q], Integrable g Q := fun Q _ =>
    Integrable.of_bound hg.aestronglyMeasurable k (Filter.Eventually.of_forall fun s => by
      rw [Real.norm_eq_abs]
      exact hb s)
  have e1 : ∀ (Q : Measure α) [IsProbabilityMeasure Q], ∫ s, g s ∂Q = ∫ s, f s ∂Q - k := fun Q _ => by
    simp only [hf]
    rw [integral_add (hgint Q) (integrable_const k)]
    simp
  have e2 : ∀ (Q : Measure α) [IsProbabilityMeasure Q],
      ∫ s, f s ∂Q = ∫ t in Set.Ioc 0 (2 * k), Q.real {a | t < f a} := fun Q _ => by
    rw [(hint Q).integral_eq_integral_meas_lt (Filter.Eventually.of_forall hf0)]
    refine setIntegral_eq_of_subset_of_forall_sdiff_eq_zero measurableSet_Ioi Set.Ioc_subset_Ioi_self fun t ht => ?_
    have h2 : 2 * k < t := by
      by_contra hn
      exact ht.2 ⟨ht.1, not_lt.mp hn⟩
    have : {a | t < f a} = ∅ := by
      ext a
      simp only [Set.mem_ofPred_eq, Set.mem_empty_iff_false, iff_false, not_lt]
      linarith [hf2 a]
    rw [this]
    simp
  have hio : ∀ (Q : Measure α) [IsProbabilityMeasure Q],
      IntegrableOn (fun t => Q.real {a | t < f a}) (Set.Ioc 0 (2 * k)) := fun Q _ => by
    have hanti : Antitone fun t : ℝ => Q.real {a | t < f a} := fun t t' h =>
      measureReal_mono (fun a (ha : t' < f a) => lt_of_le_of_lt h ha) (measure_ne_top _ _)
    refine Measure.integrableOn_of_bounded (M := 1) (by rw [Real.volume_Ioc]; exact ENNReal.ofReal_ne_top) hanti.measurable.aestronglyMeasurable
      (Filter.Eventually.of_forall fun t => ?_)
    rw [Real.norm_eq_abs, abs_of_nonneg measureReal_nonneg]
    exact measureReal_le_one
  have hcon : IntegrableOn (fun _ : ℝ => ε) (Set.Ioc 0 (2 * k)) := by
    exact integrableOn_const (by rw [Real.volume_Ioc]; exact ENNReal.ofReal_ne_top) (by simp)
  have hmono : ∫ t in Set.Ioc 0 (2 * k), P.real {a | t < f a} ≤
      ∫ t in Set.Ioc 0 (2 * k), (P'.real {a | t < f a} + ε) :=
    setIntegral_mono_on (hio P) ((hio P').add hcon) measurableSet_Ioc fun t _ =>
      hB _ (measurableSet_lt measurable_const hfm)
  rw [integral_add (hio P') hcon, setIntegral_const] at hmono
  have hv : (volume : Measure ℝ).real (Set.Ioc 0 (2 * k)) = 2 * k := by
    rw [Real.volume_real_Ioc_of_le (by positivity)]
    ring
  rw [hv, smul_eq_mul] at hmono
  rw [e1 P, e1 P', e2 P, e2 P']
  linarith
theorem abs_integral_le_of_lintegral_le (P : Measure α) {u E : α → ℝ} {c T : ℝ} (hc : 0 ≤ c) (hT : 0 ≤ T)
    (hu : ∀ s, |u s| ≤ c * E s) (hTE : ∫⁻ s, ENNReal.ofReal (E s) ∂P ≤ ENNReal.ofReal T) :
    |∫ s, u s ∂P| ≤ c * T := by
  have h1 := norm_integral_le_lintegral_norm (μ := P) u
  rw [Real.norm_eq_abs] at h1
  refine h1.trans (ENNReal.toReal_le_of_le_ofReal (by positivity) ?_)
  calc ∫⁻ s, ENNReal.ofReal ‖u s‖ ∂P ≤ ∫⁻ s, ENNReal.ofReal c * ENNReal.ofReal (E s) ∂P := by
        refine lintegral_mono fun s => ?_
        rw [← ENNReal.ofReal_mul hc, Real.norm_eq_abs]
        exact ENNReal.ofReal_le_ofReal (hu s)
    _ = ENNReal.ofReal c * ∫⁻ s, ENNReal.ofReal (E s) ∂P := lintegral_const_mul' _ _ ENNReal.ofReal_ne_top
    _ ≤ ENNReal.ofReal c * ENNReal.ofReal T := by gcongr
    _ = _ := (ENNReal.ofReal_mul hc).symm
theorem integral_sub_le_of_tail (P P' : Measure α) [IsProbabilityMeasure P] [IsProbabilityMeasure P'] {ε k c T Mg : ℝ}
    (hk : 0 ≤ k) (hc : 0 ≤ c) (hT : 0 ≤ T) (hB : ∀ B, MeasurableSet B → P.real B ≤ P'.real B + ε)
    {g E : α → ℝ} (hg : Measurable g) (hb : ∀ s, |g s| ≤ Mg) (hE : ∀ s, 0 ≤ E s) (hgk : ∀ s, |g s| - k ≤ c * E s)
    (hTE : ∫⁻ s, ENNReal.ofReal (E s) ∂P ≤ ENNReal.ofReal T) (hTE' : ∫⁻ s, ENNReal.ofReal (E s) ∂P' ≤ ENNReal.ofReal T) :
    ∫ s, g s ∂P - ∫ s, g s ∂P' ≤ 2 * k * ε + 2 * (c * T) := by
  have hcm : Measurable fun s => truncateAt k (g s) := (measurable_truncateAt k).comp hg
  have h1 := integral_sub_le_of_measureReal_le P P' hk hB hcm fun s => abs_truncateAt_le hk _
  have hint : ∀ (Q : Measure α) [IsProbabilityMeasure Q], Integrable g Q := fun Q _ =>
    Integrable.of_bound hg.aestronglyMeasurable Mg (Filter.Eventually.of_forall fun s => by
      rw [Real.norm_eq_abs]
      exact hb s)
  have hcint : ∀ (Q : Measure α) [IsProbabilityMeasure Q], Integrable (fun s => truncateAt k (g s)) Q := fun Q _ =>
    Integrable.of_bound hcm.aestronglyMeasurable k (Filter.Eventually.of_forall fun s => by
      rw [Real.norm_eq_abs]
      exact abs_truncateAt_le hk _)
  have ht : ∀ s, |g s - truncateAt k (g s)| ≤ c * E s := fun s =>
    abs_sub_truncateAt_le hk (mul_nonneg hc (hE s)) (hgk s)
  have h2 := abs_integral_le_of_lintegral_le P hc hT ht hTE
  have h3 := abs_integral_le_of_lintegral_le P' hc hT ht hTE'
  rw [integral_sub (hint P) (hcint P)] at h2
  rw [integral_sub (hint P') (hcint P')] at h3
  have a2 := (abs_le.mp h2).2
  have a3 := (abs_le.mp h3).1
  linarith
theorem abs_integral_tilted_sub_le (P Q : Measure α) [IsProbabilityMeasure P] [IsProbabilityMeasure Q] {a : α} (ha : MeasurableSet {a})
    {f g : α → ℝ} {c Y₀ e X z Mg : ℝ} (hY : 0 < Y₀) (he : 0 ≤ e) (hz : z ≤ 1 / 2) (hPa : P.real {a}ᶜ ≤ z) (hfm : Measurable f)
    (hgm : Measurable g) (hb : ∀ s, |g s| ≤ Mg) (hga : g a = 0) (hfa : f a = Y₀) (hf0 : ∀ᵐ s ∂P, 0 ≤ f s)
    (hfe : ∀ᵐ s ∂P, |f s - Y₀| ≤ e * Y₀) (hX : ∫ s, |g s| ∂P ≤ X)
    (hrep : ∀ u : α → ℝ, ∫ s, u s ∂Q = c * ∫ s, f s * u s ∂P) :
    |∫ s, g s ∂Q - ∫ s, g s ∂P| ≤ 3 * e * X := by
  classical
  have hgi : Integrable g P := Integrable.of_bound hgm.aestronglyMeasurable Mg (Filter.Eventually.of_forall fun s => by
    rw [Real.norm_eq_abs]
    exact hb s)
  have hfb : ∀ᵐ s ∂P, ‖f s‖ ≤ (e + 1) * Y₀ := by
    filter_upwards [hf0, hfe] with s h0 h1
    rw [Real.norm_eq_abs, abs_of_nonneg h0]
    have := (abs_le.mp h1).2
    nlinarith
  have hfi : Integrable f P := Integrable.of_bound hfm.aestronglyMeasurable _ hfb
  set δ : α → ℝ := fun s => f s - Y₀ with hδ
  have hδi : Integrable δ P := hfi.sub (integrable_const Y₀)
  have hδg : Integrable (fun s => δ s * g s) P :=
    Integrable.of_bound ((hfm.sub measurable_const).mul hgm).aestronglyMeasurable (e * Y₀ * Mg) (by
      filter_upwards [hfe] with s h1
      rw [Real.norm_eq_abs, abs_mul]
      exact mul_le_mul h1 (hb s) (abs_nonneg _) (by positivity))
  have hX0 : 0 ≤ X := (integral_nonneg fun s => abs_nonneg _).trans hX
  set N := ∫ s, g s ∂P with hN
  have hNX : |N| ≤ X := (abs_integral_le_integral_abs).trans hX
  set Δ := ∫ s, δ s ∂P with hΔ
  set Dn := ∫ s, f s ∂P with hDn
  have eDn : Dn = Y₀ + Δ := by
    simp only [hDn, hΔ, hδ]
    rw [integral_sub hfi (integrable_const Y₀)]
    simp
  have hc1 : c * Dn = 1 := by
    have := hrep fun _ => 1
    simp only [integral_const, probReal_univ, smul_eq_mul, mul_one] at this
    exact this.symm
  have hfg : ∫ s, f s * g s ∂P = Y₀ * N + ∫ s, δ s * g s ∂P := by
    have : ∀ s, f s * g s = Y₀ * g s + δ s * g s := fun s => by
      simp only [hδ]
      ring
    simp only [this]
    rw [integral_add (hgi.const_mul Y₀) hδg, integral_const_mul]
  have hq : ∫ s, g s ∂Q = c * (Y₀ * N + ∫ s, δ s * g s ∂P) := by
    rw [hrep g, hfg]
  have hDn2 : Y₀ / 2 ≤ Dn := by
    have h1 : ∫ s, ({a} : Set α).indicator (fun _ => Y₀) s ∂P ≤ Dn := by
      refine integral_mono_ae ((integrable_const Y₀).indicator ha) hfi ?_
      filter_upwards [hf0] with s h0
      by_cases hs : s ∈ ({a} : Set α)
      · rw [Set.indicator_of_mem hs, Set.mem_singleton_iff.mp hs, hfa]
      · rw [Set.indicator_of_notMem hs]
        exact h0
    rw [integral_indicator ha, setIntegral_const, smul_eq_mul] at h1
    have h2 : P.real {a} = 1 - P.real {a}ᶜ := by
      rw [probReal_compl_eq_one_sub ha]
      ring
    have h3 : 1 / 2 ≤ P.real {a} := by linarith
    nlinarith
  have hDnpos : 0 < Dn := by linarith
  have hcDn : c = 1 / Dn := by
    field_simp
    exact hc1
  have hΔz : |Δ| ≤ e * Y₀ / 2 := by
    have h1 : |Δ| ≤ ∫ s, |δ s| ∂P := abs_integral_le_integral_abs
    have h2 : ∫ s, |δ s| ∂P ≤ ∫ s, ({a}ᶜ : Set α).indicator (fun _ => e * Y₀) s ∂P := by
      refine integral_mono_ae hδi.abs ((integrable_const _).indicator ha.compl) ?_
      filter_upwards [hfe] with s h1
      by_cases hs : s ∈ ({a}ᶜ : Set α)
      · rw [Set.indicator_of_mem hs]
        exact h1
      · rw [Set.indicator_of_notMem hs]
        have : s = a := by simpa using hs
        subst this
        simp [hδ, hfa]
    rw [integral_indicator ha.compl, setIntegral_const, smul_eq_mul] at h2
    have h3 : 0 ≤ e * Y₀ := by positivity
    nlinarith
  have hδgX : |∫ s, δ s * g s ∂P| ≤ e * Y₀ * X := by
    have h1 : |∫ s, δ s * g s ∂P| ≤ ∫ s, |δ s * g s| ∂P := abs_integral_le_integral_abs
    have h2 : ∫ s, |δ s * g s| ∂P ≤ ∫ s, e * Y₀ * |g s| ∂P := by
      refine integral_mono_ae hδg.abs (hgi.abs.const_mul _) ?_
      filter_upwards [hfe] with s h1
      rw [abs_mul]
      exact mul_le_mul_of_nonneg_right h1 (abs_nonneg _)
    rw [integral_const_mul] at h2
    have h3 : 0 ≤ e * Y₀ := by positivity
    nlinarith
  have key : ∫ s, g s ∂Q - N = ((∫ s, δ s * g s ∂P) - N * Δ) / Dn := by
    rw [hq, hcDn]
    field_simp
    rw [eDn]
    ring
  rw [key, abs_div, abs_of_pos hDnpos, div_le_iff₀ hDnpos]
  have h1 : |(∫ s, δ s * g s ∂P) - N * Δ| ≤ e * Y₀ * X + X * (e * Y₀ / 2) := by
    refine (abs_sub _ _).trans (add_le_add hδgX ?_)
    rw [abs_mul]
    exact mul_le_mul hNX hΔz (abs_nonneg _) hX0
  have h2 : 0 ≤ 3 * e * X := by positivity
  nlinarith
end General
end Analysis
section SingleSite
section OneSpin
variable {I : Type} [Fintype I] [DecidableEq I] {S : I → Type} [∀ i, MeasurableSpace (S i)]
theorem isAdmissible_update_vacant (A : PairConstraint S) {σ : ∀ i, S i} (hσ : A.IsAdmissible σ) (i : I) :
    A.IsAdmissible (Function.update σ i (A.vacant i)) := by apply _root_.YangMills.Construction.Dobrushin.VacantSpin.isAdmissible_update_vacant <;> assumption
theorem conditionalMass_bounds (A : PairConstraint S) (m : ∀ i, Measure (S i)) {W : (∀ i, S i) → ℝ} {z : I → ℝ}
    (hW : A.IsActivityBounded m W z) (i : I) {σ : ∀ i, S i} (hσ : A.IsAdmissible σ) :
    0 < A.weightDensity W (Function.update σ i (A.vacant i)) ∧
      A.weightDensity W (Function.update σ i (A.vacant i)) ≤ A.conditionalMass m W i σ ∧ A.conditionalMass m W i σ ≠ ⊤ := by
  classical
  set d : S i → ℝ≥0∞ := fun s => A.weightDensity W (Function.update σ i s) with hd
  have hadm := isAdmissible_update_vacant A hσ i
  have hd0 : d (A.vacant i) = ENNReal.ofReal (W (Function.update σ i (A.vacant i))) := by
    simp only [hd, PairConstraint.weightDensity, if_pos hadm]
  have hpos : 0 < d (A.vacant i) := by
    rw [hd0]
    exact ENNReal.ofReal_pos.mpr (hW.pos_of_admissible _ hadm)
  have hfin : d (A.vacant i) ≠ ⊤ := by
    rw [hd0]
    exact ENNReal.ofReal_ne_top
  have h1 : ∫⁻ s in {A.vacant i}, d s ∂m i = d (A.vacant i) := by
    rw [setLIntegral_congr_fun (hW.measurableSet_vacant i) (g := fun _ => d (A.vacant i))
      (fun s hs => by rw [Set.mem_singleton_iff.mp hs]), setLIntegral_const, hW.measure_vacant i, mul_one]
  have hsplit := lintegral_add_compl d (μ := m i) (hW.measurableSet_vacant i)
  have hsm := hW.lintegral_compl_vacant_le i σ hσ
  have hM : A.conditionalMass m W i σ = ∫⁻ s, d s ∂m i := rfl
  refine ⟨hpos, ?_, ?_⟩
  · rw [hM, ← hsplit, h1]
    exact le_self_add
  · rw [hM, ← hsplit, h1]
    refine ENNReal.add_ne_top.mpr ⟨hfin, ne_top_of_le_ne_top ?_ hsm⟩
    exact ENNReal.mul_ne_top ENNReal.ofReal_ne_top hfin
theorem singleSiteLaw_eq (A : PairConstraint S) (m : ∀ i, Measure (S i)) {W : (∀ i, S i) → ℝ} {z : I → ℝ}
    (hW : A.IsActivityBounded m W z) (i : I) {σ : ∀ i, S i} (hσ : A.IsAdmissible σ) :
    A.singleSiteLaw m W i σ = (A.conditionalMass m W i σ)⁻¹ • (m i).withDensity fun s => A.weightDensity W (Function.update σ i s) := by
  obtain ⟨h0, h1, h2⟩ := conditionalMass_bounds A m hW i hσ
  unfold PairConstraint.singleSiteLaw
  rw [if_pos ⟨lt_of_lt_of_le h0 h1, h2⟩]
theorem lintegral_singleSiteKernel_le (A : PairConstraint S) (m : ∀ i, Measure (S i)) [∀ i, SigmaFinite (m i)] {W : (∀ i, S i) → ℝ}
    {z : I → ℝ} (hW : A.IsActivityBounded m W z) (i : I) {σ : ∀ i, S i} (hσ : A.IsAdmissible σ) {u : S i → ℝ} (hum : Measurable u)
    (habs : u (A.vacant i) = 0) {X : ℝ}
    (hu : ∫⁻ s in {A.vacant i}ᶜ, ENNReal.ofReal (u s) * A.weightDensity W (Function.update σ i s) ∂m i ≤
      ENNReal.ofReal X * A.weightDensity W (Function.update σ i (A.vacant i))) :
    ∫⁻ s, ENNReal.ofReal (u s) ∂(A.singleSiteKernel m hW.measurable_weightDensity i σ) ≤ ENNReal.ofReal X := by
  classical
  obtain ⟨h0, h1, h2⟩ := conditionalMass_bounds A m hW i hσ
  set d : S i → ℝ≥0∞ := fun s => A.weightDensity W (Function.update σ i s) with hd
  have hdm : Measurable d := hW.measurable_weightDensity.comp (measurable_update σ)
  have hP : (A.singleSiteKernel m hW.measurable_weightDensity i) σ = A.singleSiteLaw m W i σ := rfl
  rw [hP, singleSiteLaw_eq A m hW i hσ, lintegral_smul_measure, smul_eq_mul,
    lintegral_withDensity_eq_lintegral_mul _ hdm hum.ennreal_ofReal]
  have hsplit := lintegral_add_compl (d * fun s => ENNReal.ofReal (u s)) (μ := m i) (hW.measurableSet_vacant i)
  have habs0 : ∫⁻ s in {A.vacant i}, (d * fun s => ENNReal.ofReal (u s)) s ∂m i = 0 := by
    rw [setLIntegral_congr_fun (hW.measurableSet_vacant i) (g := fun _ => 0) (fun s hs => by
      rw [Set.mem_singleton_iff.mp hs]
      simp [habs])]
    simp
  rw [← hsplit, habs0, zero_add]
  have hle : ∫⁻ s in {A.vacant i}ᶜ, (d * fun s => ENNReal.ofReal (u s)) s ∂m i ≤ ENNReal.ofReal X * d (A.vacant i) := by
    refine le_trans (le_of_eq ?_) hu
    refine lintegral_congr fun s => ?_
    simp only [Pi.mul_apply, hd]
    ring
  have hMpos : A.conditionalMass m W i σ ≠ 0 := (lt_of_lt_of_le h0 h1).ne'
  calc (A.conditionalMass m W i σ)⁻¹ * ∫⁻ s in {A.vacant i}ᶜ, (d * fun s => ENNReal.ofReal (u s)) s ∂m i
      ≤ (A.conditionalMass m W i σ)⁻¹ * (ENNReal.ofReal X * A.conditionalMass m W i σ) := by gcongr; exact hle.trans (by gcongr)
    _ = ENNReal.ofReal X * ((A.conditionalMass m W i σ)⁻¹ * A.conditionalMass m W i σ) := by ring
    _ = ENNReal.ofReal X := by rw [ENNReal.inv_mul_cancel hMpos h2, mul_one]
theorem singleSiteKernel_tilt_density (A : PairConstraint S) (m : ∀ i, Measure (S i)) [∀ i, SigmaFinite (m i)] {W Y : (∀ i, S i) → ℝ}
    {z z' : I → ℝ} (hW : A.IsActivityBounded m W z) (hWY : A.IsActivityBounded m (fun σ => W σ * Y σ) z')
    (hpos : ∀ σ, A.IsAdmissible σ → 0 < Y σ) (hYm : Measurable Y) (i : I) {σ : ∀ i, S i} (hσ : A.IsAdmissible σ)
    (hcon : ∀ᵐ s ∂(A.singleSiteKernel m hW.measurable_weightDensity i σ), A.IsAdmissible (Function.update σ i s)) :
    ∃ c : ℝ, ∀ u : S i → ℝ, ∫ s, u s ∂(A.singleSiteKernel m hWY.measurable_weightDensity i σ) =
      c * ∫ s, Y (Function.update σ i s) * u s ∂(A.singleSiteKernel m hW.measurable_weightDensity i σ) := by
  classical
  obtain ⟨h0, h1, h2⟩ := conditionalMass_bounds A m hW i hσ
  obtain ⟨h0', h1', h2'⟩ := conditionalMass_bounds A m hWY i hσ
  set d : S i → ℝ≥0∞ := fun s => A.weightDensity W (Function.update σ i s) with hd
  set f : S i → ℝ≥0∞ := fun s => ENNReal.ofReal (Y (Function.update σ i s)) with hf
  have hdm : Measurable d := hW.measurable_weightDensity.comp (measurable_update σ)
  have hfm : Measurable f := (hYm.comp (measurable_update σ)).ennreal_ofReal
  have hd' : (fun s => A.weightDensity (fun σ => W σ * Y σ) (Function.update σ i s)) = d * f := by
    funext s
    simp only [hd, hf, Pi.mul_apply, PairConstraint.weightDensity]
    by_cases ha : A.IsAdmissible (Function.update σ i s)
    · rw [if_pos ha, if_pos ha, ENNReal.ofReal_mul (hW.pos_of_admissible _ ha).le]
    · rw [if_neg ha, if_neg ha, zero_mul]
  have hMpos : A.conditionalMass m W i σ ≠ 0 := (lt_of_lt_of_le h0 h1).ne'
  set M := A.conditionalMass m W i σ with hM
  set M' := A.conditionalMass m (fun σ => W σ * Y σ) i σ with hM'
  set P := (A.singleSiteKernel m hW.measurable_weightDensity i) σ with hPd
  have hP : P = M⁻¹ • (m i).withDensity d := singleSiteLaw_eq A m hW i hσ
  have hP' : (A.singleSiteKernel m hWY.measurable_weightDensity i) σ = M'⁻¹ • (m i).withDensity (d * f) := by
    rw [← hd']
    exact singleSiteLaw_eq A m hWY i hσ
  have hν : (m i).withDensity d = M • P := by
    rw [hP, smul_smul, ENNReal.mul_inv_cancel hMpos h2, one_smul]
  have hdf : (m i).withDensity (d * f) = M • P.withDensity f := by
    rw [withDensity_mul _ hdm hfm, hν, withDensity_smul_measure]
  refine ⟨(M'⁻¹).toReal * M.toReal, fun u => ?_⟩
  rw [hP', hdf, integral_smul_measure, integral_smul_measure,
    integral_withDensity_eq_integral_toReal_smul hfm (Filter.Eventually.of_forall fun s => ENNReal.ofReal_lt_top)]
  have : ∫ s, (f s).toReal • u s ∂P = ∫ s, Y (Function.update σ i s) * u s ∂P := by
    refine integral_congr_ae ?_
    filter_upwards [hcon] with s hs
    simp only [hf, smul_eq_mul]
    rw [ENNReal.toReal_ofReal (hpos _ hs).le]
  rw [this]
  simp only [smul_eq_mul]
  ring
theorem lintegral_gibbsLaw_single_le (hP : Dobrushin.MeanOfProductStatement) (A : PairConstraint S) (m : ∀ i, Measure (S i))
    [∀ i, SigmaFinite (m i)] {W : (∀ i, S i) → ℝ} {z : I → ℝ} (hW : A.IsActivityBounded m W z)
    [IsProbabilityMeasure (A.gibbsLaw m W)] (i : I) {ψ : S i → ℝ} (hm : Measurable ψ) (h0 : ∀ v, 0 ≤ ψ v)
    (habs : ψ (A.vacant i) = 0) {e : ℝ} (he : 0 ≤ e)
    (hex : ∀ σ, A.IsAdmissible σ → ∫⁻ s in {A.vacant i}ᶜ, ENNReal.ofReal (ψ s) * A.weightDensity W (Function.update σ i s) ∂m i ≤
      ENNReal.ofReal e * A.weightDensity W (Function.update σ i (A.vacant i))) :
    ∫⁻ σ, ENNReal.ofReal (ψ (σ i)) ∂A.gibbsLaw m W ≤ ENNReal.ofReal e := by apply _root_.YangMills.Construction.TiltedGasResponse.lintegral_single_spin_le <;> assumption
end OneSpin
end SingleSite
section SiteResponses
variable {R : StepSetup} {n : ℕ} [NeZero n] {G : GasGround R n}
section Labels
theorem spinLabelScore_nonneg {s : R.labels.Ω → ℝ} (hs : ∀ w, 0 ≤ s w) (i : G.GasSpin) (y : TorusSite (n * R.params.side))
    (v : G.SpinValue i) : 0 ≤ spinLabelScore s G i y v := by apply _root_.YangMills.Construction.ResponseInTheExpansion.FarSpin.spinLabelScore_nonneg <;> assumption
theorem measurable_spinLabelScore {s : R.labels.Ω → ℝ} (hb : Measurable s) (i : G.GasSpin) (y : TorusSite (n * R.params.side)) :
    Measurable (spinLabelScore s G i y) := by apply _root_.YangMills.Construction.TiltedGasResponse.measurable_spinLabelScore <;> assumption
theorem spinLabelScore_vacant (s : R.labels.Ω → ℝ) (i : G.GasSpin) (y : TorusSite (n * R.params.side)) :
    spinLabelScore s G i y (G.pairConstraint.vacant i) = 0 := rfl
theorem spinLabelScore_of_not_mem {s : R.labels.Ω → ℝ} {i : G.GasSpin} {y : TorusSite (n * R.params.side)} (hy : y ∉ i.1.2)
    (v : G.SpinValue i) : spinLabelScore s G i y v = 0 := by apply _root_.YangMills.Construction.ResponseInTheExpansion.FarSpin.spinLabelScore_eq_zero_of_not_mem <;> assumption
theorem sum_spinLabelScore_le_spinScore {A : ResponseSetup R} (hs : ∀ w, 0 ≤ A.score w) (B : Finset (TorusSite (n * R.params.side)))
    (i : G.GasSpin) (v : G.SpinValue i) : ∑ y ∈ B, spinLabelScore A.score G i y v ≤ WeightedResponses.spinScore A i v := by apply _root_.YangMills.Construction.TiltedGasResponse.sum_spinLabelScore_le_spinScore <;> assumption
end Labels
section Mass
variable {T : ParameterAssignment} {A : ResponseSetup R} {s : R.labels.Ω → ℝ} {Q : Finset (TorusSite n)}
  {B : Finset (TorusSite (n * R.params.side))} {e : ℝ} {Yt : G.Config → ℝ}
theorem gas_isAdmissible_update_vacant {σ : G.Config} (hσ : G.pairConstraint.IsAdmissible σ) (i : G.GasSpin) :
    G.pairConstraint.IsAdmissible (Function.update σ i (G.pairConstraint.vacant i)) := by apply _root_.YangMills.Construction.ResponseInTheExpansion.FarSpin.isAdmissible_update_vacant <;> assumption
theorem lintegral_tilted_weightDensity_le (hs : ∀ w, 0 ≤ A.score w) {c : ℝ}
    (hw : G.pairConstraint.IsActivityBounded (G.referenceMeasure ∅) G.weight (G.spinActivity c))
    (paid : ∀ (i : G.GasSpin) (σ : G.Config), G.pairConstraint.IsAdmissible σ →
      ∫⁻ v in {G.pairConstraint.vacant i}ᶜ, ENNReal.ofReal (Real.exp (WeightedResponses.spinScore A i v)) *
        G.pairConstraint.weightDensity G.weight (Function.update σ i v) ∂(G.referenceMeasure ∅ i) ≤
      ENNReal.ofReal (G.spinActivity c i) * G.pairConstraint.weightDensity G.weight (Function.update σ i (G.pairConstraint.vacant i)))
    (ht : IsGasTilt G A.score Q B e Yt) (i : G.GasSpin) {ψ : G.SpinValue i → ℝ} {Cψ : ℝ} (hC : 0 ≤ Cψ) (hψ0 : ∀ v, 0 ≤ ψ v)
    (hψ : ∀ v, ψ v * Real.exp (∑ y ∈ B, spinLabelScore A.score G i y v) ≤ Cψ * Real.exp (WeightedResponses.spinScore A i v))
    {σ : G.Config} (hσ : G.pairConstraint.IsAdmissible σ) :
    ∫⁻ v in {G.pairConstraint.vacant i}ᶜ, ENNReal.ofReal (ψ v) *
        G.pairConstraint.weightDensity (fun σ => G.weight σ * Yt σ) (Function.update σ i v) ∂(G.referenceMeasure ∅ i) ≤
      ENNReal.ofReal (3 * Cψ * G.spinActivity c i) *
        G.pairConstraint.weightDensity (fun σ => G.weight σ * Yt σ) (Function.update σ i (G.pairConstraint.vacant i)) := by apply _root_.YangMills.Construction.TiltedGasResponse.lintegral_tilted_density_le <;> assumption
theorem isActivityBounded_tilt (hs : ∀ w, 0 ≤ A.score w) {c : ℝ}
    (hw : G.pairConstraint.IsActivityBounded (G.referenceMeasure ∅) G.weight (G.spinActivity c))
    (paid : ∀ (i : G.GasSpin) (σ : G.Config), G.pairConstraint.IsAdmissible σ →
      ∫⁻ v in {G.pairConstraint.vacant i}ᶜ, ENNReal.ofReal (Real.exp (WeightedResponses.spinScore A i v)) *
        G.pairConstraint.weightDensity G.weight (Function.update σ i v) ∂(G.referenceMeasure ∅ i) ≤
      ENNReal.ofReal (G.spinActivity c i) * G.pairConstraint.weightDensity G.weight (Function.update σ i (G.pairConstraint.vacant i)))
    (ht : IsGasTilt G A.score Q B e Yt) :
    G.pairConstraint.IsActivityBounded (G.referenceMeasure ∅) (fun σ => G.weight σ * Yt σ) fun i => 3 * G.spinActivity c i := by apply _root_.YangMills.Construction.TiltedGasResponse.isActivityBounded_tilt <;> assumption
end Mass
section Means
variable {free : Finset (TorusBond (n * R.params.side))}
theorem settingMean_liveCaseFunction {s : ChartSetting R n}
    (hl : ∀ η, s.InBalls η → IsLiveState R.params R.coupling R.labelWeight (s.field η) s.support s.labelling)
    (bad : Finset (TorusBond (n * R.params.side))) (F : CaseFunction R n) :
    settingMean s bad (liveCaseFunction F) =
      weightedMean (chartDensity s) fun η => F (s.field η) s.support s.labelling bad s.bases := by apply _root_.YangMills.Construction.ResponseInTheExpansion.FarSpin.settingMean_liveCase <;> assumption
theorem abs_weightedMean_le {s : ChartSetting R n} (hd : Integrable (chartDensity s)) (hm : 0 < ∫ η, chartDensity s η)
    {g : FreeCoords s.free → ℝ} {Q : ℝ} (hQ : ∀ η, s.InBalls η → |g η| ≤ Q) :
    |weightedMean (chartDensity s) g| ≤ Q := by apply _root_.YangMills.Construction.ResponseInTheExpansion.FarSpin.abs_weightedMean_le <;> assumption
end Means
section Atoms
def siteResponse (A : ResponseSetup R) (G : GasGround R n) (f : PlaquetteWeight (fineSide R.params.side R.depth (n * R.params.side)))
    (y : TorusSite (n * R.params.side)) (σ : G.Config) : ℝ :=
  settingMean (configSetting G σ) (G.badBondsOf σ)
    (liveCaseFunction fun W Yt ωt _ _ => centeredHullResponse A.cold A.hull (n * R.params.side) y W Yt ωt f)
def siteScoreOf (A : ResponseSetup R) (G : GasGround R n) (y : TorusSite (n * R.params.side)) (σ : G.Config) : ℝ :=
  siteScore A.score (configSetting G σ).support (configSetting G σ).labelling y
structure FarTiltContext (A : ResponseSetup R) (G : GasGround R n) : Prop where
  response : A.IsAdmissible
  params_admissible : R.params.Admissible
  side_odd : Odd R.params.side
  hullExpansion : HullExpansion R.params R.depth R.coupling R.functional R.density R.labels R.labelWeight R.clusterFactor R.siteDensity
  blockSide : IsBlockTorusSide R.params (n * R.params.side)
  n₀_le : R.params.n₀ ≤ n
  functional_trivial_pos : 0 < R.functional (n * R.params.side) (trivialField (n * R.params.side))
  setting_admissible : ∀ σ, G.pairConstraint.IsAdmissible σ → (configSetting G σ).IsAdmissible
  chartDensity_facts : ∀ σ, G.pairConstraint.IsAdmissible σ → Integrable (chartDensity (configSetting G σ)) ∧
    0 < ∫ η, chartDensity (configSetting G σ) η
  settingsAgree : StepSettings.LocalSettingsAgree
  settingMean_measurable : ∀ F : CaseFunction R n, (∀ (Yt : Finset (TorusSite (n * R.params.side)))
    (bad : Finset (TorusBond (n * R.params.side))) (b : StepCosts.BaseChoice R.params.side n),
    Measurable fun p : TorusField (n * R.params.side) × (Yt → R.labels.Ω) => F p.1 Yt p.2 bad b) →
    open Classical in Measurable fun σ : G.Config =>
      if G.pairConstraint.IsAdmissible σ then settingMean (configSetting G σ) (G.badBondsOf σ) F else 0
  one_le_coupling : 1 ≤ R.params.coupling
  C₀_ge : 12 + 40 * R.params.coupling ≤ A.responseParams.C₀
  chartResponse_near : ∀ (s s' : ChartSetting R n) (Y : TorusSite n) (m : ℕ), s.IsAdmissible → s'.IsAdmissible →
    SettingsAgreeNear s s' Y Y m → (R.range : ℝ) / (4 * R.params.side) ≤ m →
    ∀ o, o ∈ centredCube R.params.side → ∀ h : PlaquetteWeight (fineSide R.params.side R.depth (n * R.params.side)),
      |chartResponse A s (fineSite R.params.side Y 0 o) h - chartResponse A s' (fineSite R.params.side Y 0 o) h| ≤
        (1 + chartSiteScore A s (fineSite R.params.side Y 0 o)) * Real.exp (-(R.params.rt * m / 2 ^ 5)) *
          weightNorm R.params.side R.depth h
variable {A : ResponseSetup R}
theorem FarTiltContext.isLiveState (h : FarTiltContext A G) {σ : G.Config} (hσ : G.pairConstraint.IsAdmissible σ)
    (η : FreeCoords (configSetting G σ).free) (hη : (configSetting G σ).InBalls η) :
    IsLiveState R.params R.coupling R.labelWeight ((configSetting G σ).field η) (configSetting G σ).support
      (configSetting G σ).labelling := by
  have hs := h.setting_admissible σ hσ
  have hh : IsHullState R.params (clusterRange R.coupling) ((configSetting G σ).field η) (configSetting G σ).support :=
    hs.isHull η hη
  refine ⟨hh, ?_⟩
  rw [h.hullExpansion.form (n * R.params.side) h.blockSide _ _ _ hh]
  have hΦ : 0 < ∏ X ∈ chainComponents (clusterRange R.coupling) (configSetting G σ).support,
      R.clusterFactor (n * R.params.side) ((configSetting G σ).field η) (configSetting G σ).support
        (configSetting G σ).labelling X := by
    refine Finset.prod_pos fun X hX => ?_
    exact lt_of_le_of_ne (h.hullExpansion.factor_nonneg (n * R.params.side) h.blockSide _ _ _ X)
      (Ne.symm (hs.factor_ne_zero η hη X hX))
  have := h.functional_trivial_pos
  positivity
theorem FarTiltContext.siteScoreOf_nonneg (h : FarTiltContext A G) (y : TorusSite (n * R.params.side)) (σ : G.Config) :
    0 ≤ siteScoreOf A G y σ :=
  siteScore_nonneg h.response.price.nonneg _ _ _
theorem FarTiltContext.siteResponse_eq (h : FarTiltContext A G) {σ : G.Config} (hσ : G.pairConstraint.IsAdmissible σ)
    (f : PlaquetteWeight (fineSide R.params.side R.depth (n * R.params.side))) (y : TorusSite (n * R.params.side)) :
    siteResponse A G f y σ = chartResponse A (configSetting G σ) y f :=
  settingMean_liveCaseFunction (fun η hη => h.isLiveState hσ η hη) _ _
theorem FarTiltContext.abs_centeredHullResponse_le (h : FarTiltContext A G) {σ : G.Config}
    (hσ : G.pairConstraint.IsAdmissible σ) {f : PlaquetteWeight (fineSide R.params.side R.depth (n * R.params.side))}
    (hsz : weightNorm R.params.side R.depth f ≤ 1) (y : TorusSite (n * R.params.side))
    (η : FreeCoords (configSetting G σ).free) (hη : (configSetting G σ).InBalls η) :
    |centeredHullResponse A.cold A.hull (n * R.params.side) y ((configSetting G σ).field η) (configSetting G σ).support
      (configSetting G σ).labelling f| ≤ A.responseParams.C₀ + siteScoreOf A G y σ := by
  have h1 := h.response.bounds.size_hull (n * R.params.side) h.blockSide y _ _ _ (h.isLiveState hσ η hη) f
  have hC : 0 ≤ A.responseParams.C₀ := by
    have h3 := h.one_le_coupling
    have h4 := h.C₀_ge
    linarith
  have h2 : 0 ≤ A.responseParams.C₀ + siteScoreOf A G y σ := add_nonneg hC (h.siteScoreOf_nonneg y σ)
  calc _ ≤ _ := h1
    _ ≤ (A.responseParams.C₀ + siteScoreOf A G y σ) * 1 := mul_le_mul_of_nonneg_left hsz h2
    _ = _ := mul_one _
theorem setGap_le {X X' : Finset (TorusSite n)} {y y' : TorusSite n} (hy : y ∈ X) (hy' : y' ∈ X') :
    setGap X X' ≤ _root_.YangMills.Construction.TorusFields.supDist y y' :=
  Nat.sInf_le ⟨y, hy, y', hy', rfl⟩
theorem exists_supDist_eq_setGap {X X' : Finset (TorusSite n)} (hX : X.Nonempty) (hX' : X'.Nonempty) :
    ∃ y ∈ X, ∃ y' ∈ X', _root_.YangMills.Construction.TorusFields.supDist y y' = setGap X X' := by apply _root_.YangMills.Construction.CoreColumns.setGap_attained <;> assumption
theorem core_nonempty (j : G.GasSpin) : j.1.core.Nonempty := by apply _root_.YangMills.Construction.StepGas.core_nonempty_of_gasSpin <;> assumption
theorem FarTiltContext.settingsAgree_update_vacant (h : FarTiltContext A G) (σ : G.Config) (j : G.GasSpin) {Y : TorusSite n}
    {m : ℕ} (hg : m + 2 ≤ setGap {Y} j.1.core) :
    SettingsAgreeNear (configSetting G σ) (configSetting G (Function.update σ j (G.pairConstraint.vacant j))) Y Y m := by
  classical
  obtain ⟨a, ha⟩ := core_nonempty j
  have h1 : setGap {Y} j.1.core ≤ _root_.YangMills.Construction.TorusFields.supDist Y a := setGap_le (Finset.mem_singleton_self Y) ha
  have h2 := SettingShifts.two_mul_supDist_le Y a
  refine h.settingsAgree R n G σ _ Y m h.side_odd (by omega) fun i hi => ?_
  obtain ⟨e, he, hc⟩ := hi
  by_cases hij : i = j
  · subst hij
    exfalso
    have h3 : setGap {Y} i.1.core ≤ _root_.YangMills.Construction.TorusFields.supDist Y (Y + siteOfInt e) := setGap_le (Finset.mem_singleton_self Y) hc
    have h4 : _root_.YangMills.Construction.TorusFields.supDist Y (Y + siteOfInt e) ≤ m := _root_.YangMills.Construction.TorusFields.supDist_add_siteOfInt_le Y e m fun l => by
      have h1 : |e l| ≤ (m : ℤ) := he l
      rw [Int.abs_eq_natAbs] at h1
      omega
    omega
  · rw [Function.update_of_ne hij]
theorem FarTiltContext.measurableSet_isLiveState (h : FarTiltContext A G) (Yt : Finset (TorusSite (n * R.params.side))) :
    MeasurableSet {p : TorusField (n * R.params.side) × (Yt → R.labels.Ω) |
      IsLiveState R.params R.coupling R.labelWeight p.1 Yt p.2} := by
  classical
  have hb := (h.hullExpansion.borel (n * R.params.side) h.blockSide Yt).1
  have e : {p : TorusField (n * R.params.side) × (Yt → R.labels.Ω) | IsLiveState R.params R.coupling R.labelWeight p.1 Yt p.2} =
      (fun p : TorusField (n * R.params.side) × (Yt → R.labels.Ω) =>
        if IsHullState R.params (clusterRange R.coupling) p.1 Yt then R.labelWeight (n * R.params.side) p.1 Yt p.2 else 0) ⁻¹'
          Set.Ioi 0 := by
    ext p
    simp only [Set.mem_setOf_eq, Set.mem_preimage, Set.mem_Ioi, IsLiveState]
    by_cases hh : IsHullState R.params (clusterRange R.coupling) p.1 Yt
    · simp [hh]
    · simp [hh]
  rw [e]
  exact hb measurableSet_Ioi
theorem FarTiltContext.measurable_liveCaseFunction_centered (h : FarTiltContext A G)
    (f : PlaquetteWeight (fineSide R.params.side R.depth (n * R.params.side))) (y : TorusSite (n * R.params.side))
    (Yt : Finset (TorusSite (n * R.params.side))) (bad : Finset (TorusBond (n * R.params.side)))
    (b : StepCosts.BaseChoice R.params.side n) :
    Measurable fun p : TorusField (n * R.params.side) × (Yt → R.labels.Ω) =>
      liveCaseFunction (R := R) (n := n) (fun W Yt ωt _ _ => centeredHullResponse A.cold A.hull (n * R.params.side) y W Yt ωt f)
        p.1 Yt p.2 bad b := by
  classical
  have h1 := h.response.bounds.hull_borel (n * R.params.side) h.blockSide y Yt f
  have h2 := h.measurableSet_isLiveState Yt
  have h3 : Measurable fun p : TorusField (n * R.params.side) × (Yt → R.labels.Ω) =>
      if IsLiveState R.params R.coupling R.labelWeight p.1 Yt p.2 then
        A.cold (n * R.params.side) y (trivialField (n * R.params.side)) f else 0 :=
    Measurable.ite h2 measurable_const measurable_const
  have h4 := h1.sub h3
  have e : (fun p : TorusField (n * R.params.side) × (Yt → R.labels.Ω) =>
      liveCaseFunction (R := R) (n := n) (fun W Yt ωt _ _ => centeredHullResponse A.cold A.hull (n * R.params.side) y W Yt ωt f)
        p.1 Yt p.2 bad b) =
      ((fun p : TorusField (n * R.params.side) × (Yt → R.labels.Ω) =>
        if IsLiveState R.params R.coupling R.labelWeight p.1 Yt p.2 then A.hull (n * R.params.side) y p.1 Yt p.2 f else 0) -
      fun p : TorusField (n * R.params.side) × (Yt → R.labels.Ω) =>
        if IsLiveState R.params R.coupling R.labelWeight p.1 Yt p.2 then
          A.cold (n * R.params.side) y (trivialField (n * R.params.side)) f else 0) := by
    funext p
    simp only [Pi.sub_apply, liveCaseFunction]
    by_cases hl : IsLiveState R.params R.coupling R.labelWeight p.1 Yt p.2
    · simp only [if_pos hl]
      rfl
    · simp only [if_neg hl, sub_zero]
  rw [e]
  exact h4
theorem FarTiltContext.measurable_siteResponse (h : FarTiltContext A G)
    (f : PlaquetteWeight (fineSide R.params.side R.depth (n * R.params.side))) (y : TorusSite (n * R.params.side)) :
    open Classical in Measurable fun σ => if G.pairConstraint.IsAdmissible σ then siteResponse A G f y σ else 0 :=
  h.settingMean_measurable _ fun Yt bad b => h.measurable_liveCaseFunction_centered f y Yt bad b
def siteLabelSum (A : ResponseSetup R) (G : GasGround R n) (y : TorusSite (n * R.params.side)) (σ : G.Config) : ℝ :=
  ∑ i, spinLabelScore A.score G i y (σ i)
theorem FarTiltContext.siteScoreOf_le (h : FarTiltContext A G) (y : TorusSite (n * R.params.side)) (σ : G.Config) :
    siteScoreOf A G y σ ≤ recordedSiteScore A G y + siteLabelSum A G y σ :=
  FreeEnergies.siteScore_configSetting_le h.response.price.nonneg σ y
theorem FarTiltContext.abs_siteResponse_le (h : FarTiltContext A G) {σ : G.Config} (hσ : G.pairConstraint.IsAdmissible σ)
    {f : PlaquetteWeight (fineSide R.params.side R.depth (n * R.params.side))} (hsz : weightNorm R.params.side R.depth f ≤ 1)
    (y : TorusSite (n * R.params.side)) :
    |siteResponse A G f y σ| ≤ A.responseParams.C₀ + siteScoreOf A G y σ := by
  obtain ⟨hdi, hdm⟩ := h.chartDensity_facts σ hσ
  have e : siteResponse A G f y σ = weightedMean (chartDensity (configSetting G σ)) (fun η =>
      centeredHullResponse A.cold A.hull (n * R.params.side) y ((configSetting G σ).field η) (configSetting G σ).support
        (configSetting G σ).labelling f) :=
    settingMean_liveCaseFunction (s := configSetting G σ) (fun η hη => h.isLiveState hσ η hη) (G.badBondsOf σ)
      (fun W Yt ωt _ _ => centeredHullResponse A.cold A.hull (n * R.params.side) y W Yt ωt f)
  rw [e]
  exact abs_weightedMean_le hdi hdm fun η hη => h.abs_centeredHullResponse_le hσ hsz y η hη
theorem update_vacant_eq {σ σ' : G.Config} {j : G.GasSpin} (hd : ∀ k, k ≠ j → σ k = σ' k) :
    Function.update σ j (G.pairConstraint.vacant j) = Function.update σ' j (G.pairConstraint.vacant j) := by apply _root_.YangMills.Construction.ResponseInTheExpansion.FarSpin.update_vacant_eq <;> assumption
theorem FarTiltContext.abs_siteResponse_sub_le (h : FarTiltContext A G) {σ σ' : G.Config}
    (hσ : G.pairConstraint.IsAdmissible σ) (hσ' : G.pairConstraint.IsAdmissible σ')
    {j : G.GasSpin} (hd : ∀ k, k ≠ j → σ k = σ' k) {f : PlaquetteWeight (fineSide R.params.side R.depth (n * R.params.side))}
    (hsz : weightNorm R.params.side R.depth f ≤ 1) {y : TorusSite (n * R.params.side)} {m : ℕ}
    (hm : (R.range : ℝ) / (4 * R.params.side) ≤ m) (hg : m + 2 ≤ setGap {parentBlock R.params.side y} j.1.core) :
    |siteResponse A G f y σ - siteResponse A G f y σ'| ≤
      (2 + siteScoreOf A G y σ + siteScoreOf A G y σ') * Real.exp (-(R.params.rt * m / 2 ^ 5)) := by
  obtain ⟨o, ho, hyo⟩ := BlockOffsets.exists_fineSite_of_parentBlock h.side_odd (parentBlock R.params.side y) y rfl
  set σ₀ := Function.update σ j (G.pairConstraint.vacant j) with hσ₀
  have h0 : G.pairConstraint.IsAdmissible σ₀ := gas_isAdmissible_update_vacant hσ j
  have a1 := h.settingsAgree_update_vacant (A := A) σ j hg
  have a2 := h.settingsAgree_update_vacant (A := A) σ' j hg
  rw [← update_vacant_eq hd] at a2
  have b1 := h.chartResponse_near _ _ _ m (h.setting_admissible σ hσ) (h.setting_admissible _ h0) a1 hm o ho f
  have b2 := h.chartResponse_near _ _ _ m (h.setting_admissible σ' hσ') (h.setting_admissible _ h0) a2 hm o ho f
  rw [← hyo] at b1 b2
  rw [h.siteResponse_eq hσ, h.siteResponse_eq hσ']
  set E := Real.exp (-(R.params.rt * m / 2 ^ 5)) with hE
  have hE0 : 0 ≤ E := (Real.exp_pos _).le
  have c1 : (1 + chartSiteScore A (configSetting G σ) y) * E * weightNorm R.params.side R.depth f ≤
      (1 + siteScoreOf A G y σ) * E := by
    have : 0 ≤ (1 + siteScoreOf A G y σ) * E := mul_nonneg (by linarith [h.siteScoreOf_nonneg y σ]) hE0
    calc _ ≤ (1 + siteScoreOf A G y σ) * E * 1 := mul_le_mul_of_nonneg_left hsz this
      _ = _ := mul_one _
  have c2 : (1 + chartSiteScore A (configSetting G σ') y) * E * weightNorm R.params.side R.depth f ≤
      (1 + siteScoreOf A G y σ') * E := by
    have : 0 ≤ (1 + siteScoreOf A G y σ') * E := mul_nonneg (by linarith [h.siteScoreOf_nonneg y σ']) hE0
    calc _ ≤ (1 + siteScoreOf A G y σ') * E * 1 := mul_le_mul_of_nonneg_left hsz this
      _ = _ := mul_one _
  calc _ ≤ |chartResponse A (configSetting G σ) y f - chartResponse A (configSetting G σ₀) y f| +
        |chartResponse A (configSetting G σ') y f - chartResponse A (configSetting G σ₀) y f| := by
        rw [abs_sub_comm (chartResponse A (configSetting G σ') y f)]
        exact abs_sub_le _ _ _
    _ ≤ (1 + siteScoreOf A G y σ) * E + (1 + siteScoreOf A G y σ') * E := add_le_add (b1.trans c1) (b2.trans c2)
    _ = _ := by ring
end Atoms
end SiteResponses
section Geometry
variable {R : StepSetup} {n : ℕ} [NeZero n] {G : GasGround R n}
section Numbers
def columnRate (R : StepSetup) : ℝ := R.params.rt / 2 ^ 6
def tiltNearFactor (R : StepSetup) : ℝ := Real.exp (2 * columnRate R * ((R.range : ℝ) / (4 * R.params.side) + 3))
def nearRadius (R : StepSetup) : ℝ := (nearGap R.params.side R.range : ℝ) + (R.range : ℝ) / (4 * R.params.side) + 3
def clusterNearFactor (R : StepSetup) : ℝ := Real.exp (columnRate R * (nearRadius R + 4))
theorem near_bound_arith {C z N r dm Gq dj Th : ℝ} (hC : 0 ≤ C) (hz : 0 ≤ z) (hN : 1 ≤ N) (hr : 0 ≤ r) (hdm : 0 ≤ dm)
    (hd : dj ≤ Gq + dm) (hG : Gq ≤ Th) :
    2 * (C * (3 * z)) ≤ 20 * C * Real.exp (r * (Th + 4)) * (z * N * Real.exp (2 * r * dm)) * Real.exp (-(r * dj)) := by
  have h1 : 1 ≤ Real.exp (r * (Th + 4)) * Real.exp (2 * r * dm) * Real.exp (-(r * dj)) := by
    rw [← Real.exp_add, ← Real.exp_add]
    apply Real.one_le_exp
    have h2 : r * dj ≤ r * (Th + dm) := mul_le_mul_of_nonneg_left (by linarith) hr
    have h3 : 0 ≤ r * dm := mul_nonneg hr hdm
    nlinarith
  have hCz : 0 ≤ C * z := mul_nonneg hC hz
  calc 2 * (C * (3 * z)) = 6 * (C * z) * 1 := by ring
    _ ≤ 20 * (C * z) * N := by nlinarith
    _ ≤ 20 * (C * z) * N * (Real.exp (r * (Th + 4)) * Real.exp (2 * r * dm) * Real.exp (-(r * dj))) := by
        have : 0 ≤ 20 * (C * z) * N := by positivity
        nlinarith
    _ = _ := by ring
theorem far_bound_arith {C0 z N r dm Gq dj Th E ε : ℝ} (hC : 0 ≤ C0) (hz : 0 ≤ z) (hN : 1 ≤ N) (hr : 0 ≤ r) (hdm : 0 ≤ dm)
    (hG0 : 0 ≤ Gq) (hTh : 0 ≤ Th) (hd : dj ≤ Gq + dm) (hd' : Gq ≤ dj)
    (hE : E ≤ Real.exp (4 * r) * Real.exp (-(r * dj))) (hε : 2 * ε ≤ 8 * z * (N * Real.exp (-(8 * r * Gq)))) :
    2 * E * (3 * z) + (2 * (C0 + r * (Gq + dm)) * ε + 2 * (Real.exp (-(r * (Gq + dm))) * (3 * z))) ≤
      20 * (C0 + 1) * Real.exp (r * (Th + 4)) * (z * N * Real.exp (2 * r * dm)) * Real.exp (-(r * dj)) := by
  set X := Real.exp (-(r * dj)) with hX
  have hX0 : 0 < X := Real.exp_pos _
  set B := Real.exp (r * (Th + 4)) with hB
  have hB1 : Real.exp (4 * r) ≤ B := by
    apply Real.exp_le_exp.mpr
    nlinarith [mul_nonneg hr hTh]
  have hB0 : 1 ≤ B := (Real.one_le_exp (by positivity)).trans hB1
  set P := Real.exp (2 * r * dm) with hP
  have hP1 : 1 ≤ P := Real.one_le_exp (by positivity)
  have t1 : 2 * E * (3 * z) ≤ 6 * ((C0 + 1) * B * (z * N * P) * X) := by
    have a1 : E ≤ B * X := hE.trans (mul_le_mul_of_nonneg_right hB1 hX0.le)
    have a0 : 1 ≤ N * P := by nlinarith
    have a2 : 1 ≤ (C0 + 1) * (N * P) := by nlinarith
    calc 2 * E * (3 * z) = 6 * z * E := by ring
      _ ≤ 6 * z * (B * X) := by gcongr
      _ = 6 * (z * (B * X)) * 1 := by ring
      _ ≤ 6 * (z * (B * X)) * ((C0 + 1) * (N * P)) := by gcongr
      _ = _ := by ring
  have t3 : 2 * (Real.exp (-(r * (Gq + dm))) * (3 * z)) ≤ 6 * ((C0 + 1) * B * (z * N * P) * X) := by
    have a1 : Real.exp (-(r * (Gq + dm))) ≤ X := by
      apply Real.exp_le_exp.mpr
      have := mul_le_mul_of_nonneg_left hd hr
      linarith
    have a2 : 1 ≤ (C0 + 1) * B * (N * P) := by
      have : 1 ≤ (C0 + 1) * B := by nlinarith
      have h2 : 1 ≤ N * P := by nlinarith
      nlinarith
    calc 2 * (Real.exp (-(r * (Gq + dm))) * (3 * z)) = 6 * z * Real.exp (-(r * (Gq + dm))) := by ring
      _ ≤ 6 * z * X := by gcongr
      _ = 6 * (z * X) * 1 := by ring
      _ ≤ 6 * (z * X) * ((C0 + 1) * B * (N * P)) := by gcongr
      _ = _ := by ring
  have t2 : 2 * (C0 + r * (Gq + dm)) * ε ≤ 8 * ((C0 + 1) * B * (z * N * P) * X) := by
    have a1 : C0 + r * (Gq + dm) ≤ (C0 + 1) * Real.exp (r * (Gq + dm)) := by
      have h1 := Real.add_one_le_exp (r * (Gq + dm))
      have h2 : 0 ≤ r * (Gq + dm) := by positivity
      nlinarith
    have a2 : Real.exp (r * (Gq + dm)) * Real.exp (-(8 * r * Gq)) ≤ P * X := by
      rw [← Real.exp_add, hP, hX, ← Real.exp_add]
      apply Real.exp_le_exp.mpr
      have h1 := mul_le_mul_of_nonneg_left hd hr
      have h2 : 0 ≤ r * Gq := mul_nonneg hr hG0
      nlinarith
    calc 2 * (C0 + r * (Gq + dm)) * ε = (C0 + r * (Gq + dm)) * (2 * ε) := by ring
      _ ≤ (C0 + r * (Gq + dm)) * (8 * z * (N * Real.exp (-(8 * r * Gq)))) := by gcongr
      _ ≤ ((C0 + 1) * Real.exp (r * (Gq + dm))) * (8 * z * (N * Real.exp (-(8 * r * Gq)))) := by gcongr
      _ = 8 * ((C0 + 1) * z * N) * (Real.exp (r * (Gq + dm)) * Real.exp (-(8 * r * Gq))) := by ring
      _ ≤ 8 * ((C0 + 1) * z * N) * (P * X) := by gcongr
      _ = 8 * ((C0 + 1) * 1 * (z * N * P) * X) := by ring
      _ ≤ _ := by
          have : 0 ≤ (C0 + 1) * (z * N * P) * X := by positivity
          nlinarith
  have := add_le_add t1 (add_le_add t2 t3)
  calc _ ≤ _ := this
    _ = _ := by ring
end Numbers
section Gaps
theorem setGap_singleton_bounds {i : G.GasSpin} {Y : TorusSite n} (hY : Y ∈ i.1.core) (j : G.GasSpin) :
    setGap i.1.core j.1.core ≤ setGap {Y} j.1.core ∧
      setGap {Y} j.1.core ≤ setGap i.1.core j.1.core + siteDiameter i.1.core := by
  constructor
  · obtain ⟨y, hy, a, ha, e⟩ := exists_supDist_eq_setGap (X := {Y}) (Finset.singleton_nonempty Y) (core_nonempty j)
    rw [← e, Finset.mem_singleton.mp hy]
    exact setGap_le hY ha
  · obtain ⟨b, hb, a, ha, e⟩ := exists_supDist_eq_setGap (core_nonempty i) (core_nonempty j)
    have h1 : setGap {Y} j.1.core ≤ _root_.YangMills.Construction.TorusFields.supDist Y a := setGap_le (Finset.mem_singleton_self Y) ha
    have h2 := _root_.YangMills.Construction.TorusFields.supDist_triangle Y b a
    have h3 : _root_.YangMills.Construction.TorusFields.supDist Y b ≤ siteDiameter i.1.core := by
      unfold siteDiameter
      exact (Finset.le_sup (f := fun z => _root_.YangMills.Construction.TorusFields.supDist Y z) hb).trans
        (Finset.le_sup (f := fun y => i.1.core.sup fun z => _root_.YangMills.Construction.TorusFields.supDist y z) hY)
    omega
theorem setGap_le_nearGap {θ θ' : GasSupport R n} (h : ¬ θ.FarApart θ') :
    setGap θ.core θ'.core ≤ nearGap R.params.side R.range := by apply _root_.YangMills.Construction.ClusterExpansionOfAStep.GasColumns.setGap_le_nearGap <;> assumption
end Gaps
end Geometry
section SpinParts
variable {R : StepSetup} {n : ℕ} [NeZero n] {G : GasGround R n}
section Parts
variable {A : ResponseSetup R} {Q : Finset (TorusSite n)} {B : Finset (TorusSite (n * R.params.side))} {e c : ℝ}
  {Yt : G.Config → ℝ}
theorem FarTiltContext.C₀_nonneg (h : FarTiltContext A G) : 0 ≤ A.responseParams.C₀ := by
  have h3 := h.one_le_coupling
  have h4 := h.C₀_ge
  linarith
open Classical in
def expSpinLabel (A : ResponseSetup R) (G : GasGround R n) (i : G.GasSpin) (y : TorusSite (n * R.params.side))
    (v : G.SpinValue i) : ℝ :=
  if v = G.pairConstraint.vacant i then 0 else Real.exp (spinLabelScore A.score G i y v)
theorem expSpinLabel_nonneg (i : G.GasSpin) (y : TorusSite (n * R.params.side)) (v : G.SpinValue i) :
    0 ≤ expSpinLabel A G i y v := by
  classical
  unfold expSpinLabel
  split_ifs
  · exact le_rfl
  · exact (Real.exp_pos _).le
theorem expSpinLabel_vacant (i : G.GasSpin) (y : TorusSite (n * R.params.side)) :
    expSpinLabel A G i y (G.pairConstraint.vacant i) = 0 := by
  classical
  unfold expSpinLabel
  rw [if_pos rfl]
theorem measurable_expSpinLabel (hb : Measurable A.score) (i : G.GasSpin)
    (hset : MeasurableSet ({G.pairConstraint.vacant i} : Set (G.SpinValue i))) (y : TorusSite (n * R.params.side)) :
    Measurable (expSpinLabel A G i y) := by
  classical
  unfold expSpinLabel
  exact Measurable.ite hset measurable_const (Real.measurable_exp.comp (measurable_spinLabelScore hb i y))
theorem lintegral_weightDensity_le {i : G.GasSpin} {ψ : G.SpinValue i → ℝ} {Cψ : ℝ} (hC : 0 ≤ Cψ)
    (paid : ∀ (σ : G.Config), G.pairConstraint.IsAdmissible σ →
      ∫⁻ v in {G.pairConstraint.vacant i}ᶜ, ENNReal.ofReal (Real.exp (WeightedResponses.spinScore A i v)) *
        G.pairConstraint.weightDensity G.weight (Function.update σ i v) ∂(G.referenceMeasure ∅ i) ≤
      ENNReal.ofReal (G.spinActivity c i) * G.pairConstraint.weightDensity G.weight (Function.update σ i (G.pairConstraint.vacant i)))
    (hψ : ∀ v, ψ v ≤ Cψ * Real.exp (WeightedResponses.spinScore A i v)) {σ : G.Config}
    (hσ : G.pairConstraint.IsAdmissible σ) :
    ∫⁻ v in {G.pairConstraint.vacant i}ᶜ, ENNReal.ofReal (ψ v) *
        G.pairConstraint.weightDensity G.weight (Function.update σ i v) ∂(G.referenceMeasure ∅ i) ≤
      ENNReal.ofReal (Cψ * G.spinActivity c i) *
        G.pairConstraint.weightDensity G.weight (Function.update σ i (G.pairConstraint.vacant i)) := by
  calc _ ≤ ∫⁻ v in {G.pairConstraint.vacant i}ᶜ, ENNReal.ofReal Cψ * (ENNReal.ofReal (Real.exp (WeightedResponses.spinScore A i v)) *
          G.pairConstraint.weightDensity G.weight (Function.update σ i v)) ∂(G.referenceMeasure ∅ i) := by
        refine lintegral_mono fun v => ?_
        rw [← mul_assoc, ← ENNReal.ofReal_mul hC]
        gcongr
        exact hψ v
    _ = ENNReal.ofReal Cψ * ∫⁻ v in {G.pairConstraint.vacant i}ᶜ, ENNReal.ofReal (Real.exp (WeightedResponses.spinScore A i v)) *
          G.pairConstraint.weightDensity G.weight (Function.update σ i v) ∂(G.referenceMeasure ∅ i) :=
        lintegral_const_mul' _ _ ENNReal.ofReal_ne_top
    _ ≤ ENNReal.ofReal Cψ * (ENNReal.ofReal (G.spinActivity c i) *
          G.pairConstraint.weightDensity G.weight (Function.update σ i (G.pairConstraint.vacant i))) := by
        gcongr
        exact paid σ hσ
    _ = _ := by rw [ENNReal.ofReal_mul hC, mul_assoc]
def admissibleResponse (A : ResponseSetup R) (G : GasGround R n)
    (h : PlaquetteWeight (fineSide R.params.side R.depth (n * R.params.side))) (y : TorusSite (n * R.params.side))
    (σ : G.Config) : ℝ :=
  open Classical in if G.pairConstraint.IsAdmissible σ then siteResponse A G h y σ else 0
open Classical in
def truncatedSpinPart (A : ResponseSetup R) (G : GasGround R n)
    (h : PlaquetteWeight (fineSide R.params.side R.depth (n * R.params.side))) (y : TorusSite (n * R.params.side))
    (M : ℝ) (i : G.GasSpin) (σ : G.Config) : ℝ :=
  if σ i = G.pairConstraint.vacant i then 0 else truncateAt M (admissibleResponse A G h y σ)
def spinAverage (Kr : ∀ i : G.GasSpin, Kernel G.Config (G.SpinValue i)) (F : G.Config → ℝ) (i : G.GasSpin) (σ : G.Config) : ℝ :=
  ∫ s, F (Function.update σ i s) ∂(Kr i σ)
abbrev gasKernel {W : G.Config → ℝ} {z : G.GasSpin → ℝ} (hW : G.pairConstraint.IsActivityBounded (G.referenceMeasure ∅) W z)
    (i : G.GasSpin) : Kernel G.Config (G.SpinValue i) :=
  G.pairConstraint.singleSiteKernel (G.referenceMeasure ∅) hW.measurable_weightDensity i
theorem measurable_truncatedSpinPart (st : FarTiltContext A G)
    (hset : ∀ i, MeasurableSet ({G.pairConstraint.vacant i} : Set (G.SpinValue i)))
    (h : PlaquetteWeight (fineSide R.params.side R.depth (n * R.params.side))) (y : TorusSite (n * R.params.side)) (M : ℝ)
    (i : G.GasSpin) : Measurable (truncatedSpinPart A G h y M i) := by
  classical
  have h1 : Measurable (admissibleResponse A G h y) := st.measurable_siteResponse h y
  have h2 : MeasurableSet {σ : G.Config | σ i = G.pairConstraint.vacant i} := (measurable_pi_apply i) (hset i)
  exact Measurable.ite h2 measurable_const ((measurable_truncateAt M).comp h1)
theorem abs_truncatedSpinPart_le {h : PlaquetteWeight (fineSide R.params.side R.depth (n * R.params.side))}
    {y : TorusSite (n * R.params.side)} {M : ℝ} (hM : 0 ≤ M) (i : G.GasSpin) (σ : G.Config) :
    |truncatedSpinPart A G h y M i σ| ≤ M := by
  classical
  unfold truncatedSpinPart
  split_ifs
  · simpa using hM
  · exact abs_truncateAt_le hM _
theorem truncatedSpinPart_update_vacant {h : PlaquetteWeight (fineSide R.params.side R.depth (n * R.params.side))}
    {y : TorusSite (n * R.params.side)} {M : ℝ} (i : G.GasSpin) (σ : G.Config) :
    truncatedSpinPart A G h y M i (Function.update σ i (G.pairConstraint.vacant i)) = 0 := by
  classical
  unfold truncatedSpinPart
  simp
theorem recordedSiteScore_eq_zero {i : G.GasSpin} {y : TorusSite (n * R.params.side)} (hy : y ∈ i.1.2) :
    recordedSiteScore A G y = 0 := by
  classical
  unfold recordedSiteScore siteScore
  rw [dif_neg]
  intro hm
  have := i.2.far_from_anchor y (Finset.mem_union_right _ hy) y (Finset.mem_union_right _ hm)
  simp [_root_.YangMills.Construction.TorusFields.supDist_self] at this
theorem siteLabelSum_eq_single {σ : G.Config} (hσ : G.pairConstraint.IsAdmissible σ) {i : G.GasSpin}
    {y : TorusSite (n * R.params.side)} (hy : y ∈ i.1.2) (hi : σ i ≠ G.pairConstraint.vacant i) :
    siteLabelSum A G y σ = spinLabelScore A.score G i y (σ i) := by
  classical
  unfold siteLabelSum
  refine Finset.sum_eq_single i (fun j _ hj => ?_) (fun hn => absurd (Finset.mem_univ i) hn)
  by_cases hyj : y ∈ j.1.2
  · rcases hσ i j (Ne.symm hj) with h | h | h
    · exact absurd h hi
    · rw [h]
      exact spinLabelScore_vacant _ j y
    · have := h y (Finset.mem_union_right _ hy) y (Finset.mem_union_right _ hyj)
      simp [_root_.YangMills.Construction.TorusFields.supDist_self] at this
  · exact spinLabelScore_of_not_mem hyj _
theorem FarTiltContext.siteScoreOf_le_label (st : FarTiltContext A G) {σ : G.Config} (hσ : G.pairConstraint.IsAdmissible σ)
    {i : G.GasSpin} {y : TorusSite (n * R.params.side)} (hy : y ∈ i.1.2) (hi : σ i ≠ G.pairConstraint.vacant i) :
    siteScoreOf A G y σ ≤ spinLabelScore A.score G i y (σ i) := by
  have h1 := st.siteScoreOf_le y σ
  rw [recordedSiteScore_eq_zero hy, siteLabelSum_eq_single hσ hy hi, zero_add] at h1
  exact h1
theorem FarTiltContext.abs_siteResponse_le_label (st : FarTiltContext A G) {σ : G.Config}
    (hσ : G.pairConstraint.IsAdmissible σ) {i : G.GasSpin}
    {h : PlaquetteWeight (fineSide R.params.side R.depth (n * R.params.side))} (hsz : weightNorm R.params.side R.depth h ≤ 1)
    {y : TorusSite (n * R.params.side)} (hy : y ∈ i.1.2) (hi : σ i ≠ G.pairConstraint.vacant i) :
    |siteResponse A G h y σ| ≤ A.responseParams.C₀ + spinLabelScore A.score G i y (σ i) := by
  have h1 := st.abs_siteResponse_le hσ hsz y
  have h2 := st.siteScoreOf_le_label hσ hy hi
  linarith
theorem FarTiltContext.truncatedSpinPart_tail (st : FarTiltContext A G)
    {h : PlaquetteWeight (fineSide R.params.side R.depth (n * R.params.side))} (hsz : weightNorm R.params.side R.depth h ≤ 1)
    {y : TorusSite (n * R.params.side)} {i : G.GasSpin} (hy : y ∈ i.1.2) {M k : ℝ} (hM : 0 ≤ M) (hk : 0 ≤ k) (σ : G.Config) :
    |truncatedSpinPart A G h y M i σ| - k ≤ Real.exp (A.responseParams.C₀ - k) * expSpinLabel A G i y (σ i) := by
  classical
  unfold truncatedSpinPart expSpinLabel
  by_cases hi : σ i = G.pairConstraint.vacant i
  · simp only [if_pos hi]
    simpa using hk
  · simp only [if_neg hi]
    have hE : 0 ≤ Real.exp (A.responseParams.C₀ - k) * Real.exp (spinLabelScore A.score G i y (σ i)) := by positivity
    by_cases hσ : G.pairConstraint.IsAdmissible σ
    · have h1 : admissibleResponse A G h y σ = siteResponse A G h y σ := by
        unfold admissibleResponse
        rw [if_pos hσ]
      have h2 := abs_truncateAt_le_abs hM (admissibleResponse A G h y σ)
      rw [h1] at h2
      have h3 := st.abs_siteResponse_le_label hσ hsz hy hi
      rw [h1, ← Real.exp_add]
      have h4 := Real.add_one_le_exp (A.responseParams.C₀ - k + spinLabelScore A.score G i y (σ i))
      linarith
    · have h1 : admissibleResponse A G h y σ = 0 := by
        unfold admissibleResponse
        rw [if_neg hσ]
      rw [h1, truncateAt_zero hM, abs_zero]
      linarith
theorem FarTiltContext.abs_truncatedSpinPart_le_exp (st : FarTiltContext A G)
    {h : PlaquetteWeight (fineSide R.params.side R.depth (n * R.params.side))} (hsz : weightNorm R.params.side R.depth h ≤ 1)
    {y : TorusSite (n * R.params.side)} {i : G.GasSpin} (hy : y ∈ i.1.2) {M : ℝ} (hM : 0 ≤ M) (σ : G.Config) :
    |truncatedSpinPart A G h y M i σ| ≤ (A.responseParams.C₀ + 1) * expSpinLabel A G i y (σ i) := by
  classical
  have hs := st.response.price.nonneg
  have hC := st.C₀_nonneg
  unfold truncatedSpinPart expSpinLabel
  by_cases hi : σ i = G.pairConstraint.vacant i
  · simp [if_pos hi]
  · simp only [if_neg hi]
    have hl := spinLabelScore_nonneg hs i y (σ i)
    have hl1 := Real.add_one_le_exp (spinLabelScore A.score G i y (σ i))
    by_cases hσ : G.pairConstraint.IsAdmissible σ
    · have h1 : admissibleResponse A G h y σ = siteResponse A G h y σ := by
        unfold admissibleResponse
        rw [if_pos hσ]
      have h2 := abs_truncateAt_le_abs hM (admissibleResponse A G h y σ)
      rw [h1] at h2
      have h3 := st.abs_siteResponse_le_label hσ hsz hy hi
      rw [h1]
      nlinarith
    · have h1 : admissibleResponse A G h y σ = 0 := by
        unfold admissibleResponse
        rw [if_neg hσ]
      rw [h1, truncateAt_zero hM, abs_zero]
      positivity
theorem measurable_spinAverage (Kr : ∀ i : G.GasSpin, Kernel G.Config (G.SpinValue i)) (i : G.GasSpin) [IsMarkovKernel (Kr i)]
    {F : G.Config → ℝ} (hF : Measurable F) : Measurable (spinAverage Kr F i) := by
  have h1 : Measurable fun p : G.Config × G.SpinValue i => F (Function.update p.1 i p.2) := hF.comp measurable_update'
  exact h1.stronglyMeasurable.integral_kernel_prod_right'.measurable
theorem abs_spinAverage_le (Kr : ∀ i : G.GasSpin, Kernel G.Config (G.SpinValue i)) (i : G.GasSpin) [IsMarkovKernel (Kr i)]
    {F : G.Config → ℝ} {M : ℝ} (hb : ∀ σ, |F σ| ≤ M) (σ : G.Config) : |spinAverage Kr F i σ| ≤ M := by
  have := norm_integral_le_of_norm_le_const (μ := Kr i σ) (C := M) (f := fun s => F (Function.update σ i s))
    (Filter.Eventually.of_forall fun s => by
      rw [Real.norm_eq_abs]
      exact hb _)
  simpa [spinAverage, Real.norm_eq_abs] using this
theorem FarTiltContext.abs_integral_truncatedSpinPart_le (st : FarTiltContext A G)
    {h : PlaquetteWeight (fineSide R.params.side R.depth (n * R.params.side))} (hsz : weightNorm R.params.side R.depth h ≤ 1)
    {y : TorusSite (n * R.params.side)} {i : G.GasSpin} (hy : y ∈ i.1.2) {M : ℝ} (hM : 0 ≤ M) {z : ℝ} (hz : 0 ≤ z)
    (P : Measure (G.SpinValue i)) (σ : G.Config)
    (hmom : ∫⁻ s, ENNReal.ofReal (expSpinLabel A G i y s) ∂P ≤ ENNReal.ofReal (3 * z)) :
    |∫ s, truncatedSpinPart A G h y M i (Function.update σ i s) ∂P| ≤ (A.responseParams.C₀ + 1) * (3 * z) := by
  refine abs_integral_le_of_lintegral_le P (by linarith [st.C₀_nonneg]) (by positivity) (fun s => ?_) hmom
  have := st.abs_truncatedSpinPart_le_exp hsz hy hM (Function.update σ i s)
  simpa using this
end Parts
end SpinParts
section TiltedMeans
variable {R : StepSetup} {n : ℕ} [NeZero n] {G : GasGround R n}
section Means
variable {A : ResponseSetup R} {Q : Finset (TorusSite n)} {B : Finset (TorusSite (n * R.params.side))} {e c : ℝ}
  {Yt : G.Config → ℝ}
theorem FarTiltContext.abs_spinAverage_tilt_sub_le (st : FarTiltContext A G)
    {h : PlaquetteWeight (fineSide R.params.side R.depth (n * R.params.side))} (hsz : weightNorm R.params.side R.depth h ≤ 1)
    {y : TorusSite (n * R.params.side)} {i : G.GasSpin} (hy : y ∈ i.1.2) {M : ℝ} (hM : 0 ≤ M)
    {z z' : G.GasSpin → ℝ} (hw : G.pairConstraint.IsActivityBounded (G.referenceMeasure ∅) G.weight z)
    (hw' : G.pairConstraint.IsActivityBounded (G.referenceMeasure ∅) (fun σ => G.weight σ * Yt σ) z')
    (gib : G.pairConstraint.IsSpecification (G.pairConstraint.gibbsLaw (G.referenceMeasure ∅) G.weight) (gasKernel hw))
    (hYm : Measurable Yt)
    (hpos : ∀ σ, G.pairConstraint.IsAdmissible σ → 0 < Yt σ) (hz : z i ≤ 1 / 2) (hz0 : 0 ≤ z i)
    (hpres : ∀ σ, G.pairConstraint.IsAdmissible σ → (gasKernel hw i σ).real {G.pairConstraint.vacant i}ᶜ ≤ z i)
    [IsMarkovKernel (gasKernel hw' i)] {σ : G.Config} (hσ : G.pairConstraint.IsAdmissible σ)
    (hmom : ∫⁻ s, ENNReal.ofReal (expSpinLabel A G i y s) ∂(gasKernel hw i σ) ≤ ENNReal.ofReal (3 * z i)) {e' : ℝ}
    (he' : 0 ≤ e')
    (hfar : ∀ v, v ≠ G.pairConstraint.vacant i → G.pairConstraint.IsAdmissible (Function.update σ i v) →
      |Yt (Function.update σ i v) - Yt (Function.update σ i (G.pairConstraint.vacant i))| ≤
        e' * Yt (Function.update σ i (G.pairConstraint.vacant i))) :
    |spinAverage (gasKernel hw') (truncatedSpinPart A G h y M i) i σ -
        spinAverage (gasKernel hw) (truncatedSpinPart A G h y M i) i σ| ≤
      3 * e' * ((A.responseParams.C₀ + 1) * (3 * z i)) := by
  classical
  have hmk : IsMarkovKernel (gasKernel hw i) := gib.isMarkovKernel i
  have hcon := gib.ae_admissible_update i σ hσ
  obtain ⟨cc, hcc⟩ := singleSiteKernel_tilt_density G.pairConstraint (G.referenceMeasure ∅) hw hw' hpos hYm i hσ hcon
  have hset := hw.measurableSet_vacant
  have hpm := measurable_truncatedSpinPart st hset h y M i
  have hadm0 := isAdmissible_update_vacant G.pairConstraint hσ i
  have hC1 : 0 ≤ A.responseParams.C₀ + 1 := by linarith [st.C₀_nonneg]
  have hX : ∫ s, |truncatedSpinPart A G h y M i (Function.update σ i s)| ∂(gasKernel hw i σ) ≤
      (A.responseParams.C₀ + 1) * (3 * z i) := by
    have h1 := abs_integral_le_of_lintegral_le (gasKernel hw i σ)
      (u := fun s => |truncatedSpinPart A G h y M i (Function.update σ i s)|)
      (E := expSpinLabel A G i y) hC1 (by positivity) (fun s => by
        have := st.abs_truncatedSpinPart_le_exp hsz hy hM (Function.update σ i s)
        simpa using this) hmom
    exact (le_abs_self _).trans h1
  exact abs_integral_tilted_sub_le (gasKernel hw i σ) (gasKernel hw' i σ) (a := G.pairConstraint.vacant i) (hset i)
    (f := fun s => Yt (Function.update σ i s)) (g := fun s => truncatedSpinPart A G h y M i (Function.update σ i s))
    (Y₀ := Yt (Function.update σ i (G.pairConstraint.vacant i))) (Mg := M) (hpos _ hadm0) he' hz (hpres σ hσ)
    (hYm.comp (measurable_update σ)) (hpm.comp (measurable_update σ)) (fun s => abs_truncatedSpinPart_le hM i _)
    (truncatedSpinPart_update_vacant i σ) rfl
    (by filter_upwards [hcon] with s hs using (hpos _ hs).le)
    (by
      filter_upwards [hcon] with s hs
      by_cases hsa : s = G.pairConstraint.vacant i
      · subst hsa
        rw [sub_self, abs_zero]
        have := hpos _ hadm0
        positivity
      · exact hfar s hsa hs)
    hX hcc
theorem isAdmissible_update_of_allCompatible {i j : G.GasSpin} (hF : G.pairConstraint.AllCompatible i j) (hij : i ≠ j)
    {σ σ' : G.Config} (hσ' : G.pairConstraint.IsAdmissible σ') (hd : ∀ k, k ≠ j → σ k = σ' k) {s : G.SpinValue i}
    (hs : G.pairConstraint.IsAdmissible (Function.update σ i s)) :
    G.pairConstraint.IsAdmissible (Function.update σ' i s) := by
  intro a b hab
  by_cases ha : a = i
  · subst ha
    rw [Function.update_self, Function.update_of_ne hab.symm]
    by_cases hb : b = j
    · subst hb
      exact hF _ _
    · have := hs a b hab
      rw [Function.update_self, Function.update_of_ne hab.symm, hd b hb] at this
      exact this
  · by_cases hb : b = i
    · subst hb
      rw [Function.update_self, Function.update_of_ne ha]
      by_cases haj : a = j
      · subst haj
        exact G.pairConstraint.compatible_symm _ _ _ _ (hF _ _)
      · have := hs a b hab
        rw [Function.update_self, Function.update_of_ne ha, hd a haj] at this
        exact this
    · rw [Function.update_of_ne ha, Function.update_of_ne hb]
      exact hσ' a b hab
theorem FarTiltContext.abs_truncatedSpinPart_sub_le (st : FarTiltContext A G)
    {h : PlaquetteWeight (fineSide R.params.side R.depth (n * R.params.side))} (hsz : weightNorm R.params.side R.depth h ≤ 1)
    {y : TorusSite (n * R.params.side)} {i j : G.GasSpin} (hy : y ∈ i.1.2) {M : ℝ} (hM : 0 ≤ M)
    (hF : G.pairConstraint.AllCompatible i j) (hij : i ≠ j)
    {σ σ' : G.Config} (hσ : G.pairConstraint.IsAdmissible σ) (hσ' : G.pairConstraint.IsAdmissible σ')
    (hd : ∀ k, k ≠ j → σ k = σ' k) {m : ℕ}
    (hm : (R.range : ℝ) / (4 * R.params.side) ≤ m) (hg : m + 2 ≤ setGap {parentBlock R.params.side y} j.1.core)
    (s : G.SpinValue i) :
    |truncatedSpinPart A G h y M i (Function.update σ i s) - truncatedSpinPart A G h y M i (Function.update σ' i s)| ≤
      2 * Real.exp (-(R.params.rt * m / 2 ^ 5)) * expSpinLabel A G i y s := by
  classical
  have hE : 0 ≤ Real.exp (-(R.params.rt * m / 2 ^ 5)) := (Real.exp_pos _).le
  by_cases hsa : s = G.pairConstraint.vacant i
  · subst hsa
    rw [truncatedSpinPart_update_vacant, truncatedSpinPart_update_vacant, expSpinLabel_vacant]
    simp
  have hval : ∀ τ : G.Config, truncatedSpinPart A G h y M i (Function.update τ i s) =
      truncateAt M (admissibleResponse A G h y (Function.update τ i s)) := fun τ => by
    unfold truncatedSpinPart
    rw [Function.update_self, if_neg hsa]
  have hexp : expSpinLabel A G i y s = Real.exp (spinLabelScore A.score G i y s) := by
    unfold expSpinLabel
    rw [if_neg hsa]
  rw [hval, hval, hexp]
  have hEl := Real.exp_pos (spinLabelScore A.score G i y s)
  by_cases hs : G.pairConstraint.IsAdmissible (Function.update σ i s)
  · have hs' := isAdmissible_update_of_allCompatible hF hij hσ' hd hs
    have g1 : admissibleResponse A G h y (Function.update σ i s) = siteResponse A G h y (Function.update σ i s) := by
      unfold admissibleResponse
      rw [if_pos hs]
    have g2 : admissibleResponse A G h y (Function.update σ' i s) = siteResponse A G h y (Function.update σ' i s) := by
      unfold admissibleResponse
      rw [if_pos hs']
    have hdd : ∀ k, k ≠ j → Function.update σ i s k = Function.update σ' i s k := fun k hk => by
      by_cases hki : k = i
      · subst hki
        simp
      · rw [Function.update_of_ne hki, Function.update_of_ne hki, hd k hk]
    have h1 := st.abs_siteResponse_sub_le hs hs' hdd hsz hm hg
    have p1 : Function.update σ i s i ≠ G.pairConstraint.vacant i := by rwa [Function.update_self]
    have p2 : Function.update σ' i s i ≠ G.pairConstraint.vacant i := by rwa [Function.update_self]
    have l1 := st.siteScoreOf_le_label hs hy p1
    have l2 := st.siteScoreOf_le_label hs' hy p2
    rw [Function.update_self] at l1 l2
    have hl1 := Real.add_one_le_exp (spinLabelScore A.score G i y s)
    rw [g1, g2]
    refine (abs_truncateAt_sub_le hM _ _).trans (h1.trans ?_)
    have : 2 + siteScoreOf A G y (Function.update σ i s) + siteScoreOf A G y (Function.update σ' i s) ≤
        2 * Real.exp (spinLabelScore A.score G i y s) := by linarith
    calc _ ≤ 2 * Real.exp (spinLabelScore A.score G i y s) * Real.exp (-(R.params.rt * m / 2 ^ 5)) :=
          mul_le_mul_of_nonneg_right this hE
      _ = _ := by ring
  · have hs' : ¬ G.pairConstraint.IsAdmissible (Function.update σ' i s) := fun h' =>
      hs (isAdmissible_update_of_allCompatible hF hij hσ (fun k hk => (hd k hk).symm) h')
    have g1 : admissibleResponse A G h y (Function.update σ i s) = 0 := by
      unfold admissibleResponse
      rw [if_neg hs]
    have g2 : admissibleResponse A G h y (Function.update σ' i s) = 0 := by
      unfold admissibleResponse
      rw [if_neg hs']
    rw [g1, g2, sub_self, abs_zero]
    positivity
end Means
end TiltedMeans
section Oscillation
variable {R : StepSetup} {n : ℕ} [NeZero n] {G : GasGround R n}
section Osc
variable {A : ResponseSetup R} {Q : Finset (TorusSite n)} {B : Finset (TorusSite (n * R.params.side))} {e c : ℝ}
  {Yt : G.Config → ℝ}
theorem coreWeightFrom_pos (Y : TorusSite n) (j : G.GasSpin) : 0 < G.coreWeightFrom Y j := by apply _root_.YangMills.Construction.GasComparison.coreWeightFrom_pos <;> assumption
def clusterCost (A : ResponseSetup R) (G : GasGround R n) (c : ℝ) (i : G.GasSpin) : ℝ :=
  20 * (A.responseParams.C₀ + 1) * clusterNearFactor R *
    (G.spinActivity c i * (i.1.core.card : ℝ) * Real.exp (2 * columnRate R * (siteDiameter i.1.core : ℝ)))
theorem FarTiltContext.oscillationBound_spinAverage (st : FarTiltContext A G)
    {h : PlaquetteWeight (fineSide R.params.side R.depth (n * R.params.side))} (hsz : weightNorm R.params.side R.depth h ≤ 1)
    {y : TorusSite (n * R.params.side)} {i : G.GasSpin} (hy : y ∈ i.1.2) {M : ℝ} (hM : 0 ≤ M) (hrt : 0 < R.params.rt)
    (hw : G.pairConstraint.IsActivityBounded (G.referenceMeasure ∅) G.weight (G.spinActivity c))
    (cols : G.HasSmallColumns (fun j => j.1.Touches ∅) c hw)
    (gib : G.pairConstraint.IsSpecification (G.pairConstraint.gibbsLaw (G.referenceMeasure ∅) G.weight) (gasKernel hw))
    (hmom : ∀ σ, G.pairConstraint.IsAdmissible σ →
      ∫⁻ s, ENNReal.ofReal (expSpinLabel A G i y s) ∂(gasKernel hw i σ) ≤ ENNReal.ofReal (3 * G.spinActivity c i)) :
    G.pairConstraint.OscillationBound (spinAverage (gasKernel hw) (truncatedSpinPart A G h y M i) i)
      fun j => clusterCost A G c i * G.coreWeightFrom (parentBlock R.params.side y) j := by
  classical
  have hmk : ∀ i, IsMarkovKernel (gasKernel hw i) := gib.isMarkovKernel
  have hmk' := hmk i
  have hC0 := st.C₀_nonneg
  have hC1 : 0 ≤ A.responseParams.C₀ + 1 := by linarith
  have hz0 : 0 ≤ G.spinActivity c i := hw.activity_nonneg i
  have hrp : 0 < columnRate R := by unfold columnRate; positivity
  set Y := parentBlock R.params.side y with hYd
  have hYc : Y ∈ i.1.core := GasSupport.parentBlock_mem_core (Finset.mem_union_right _ hy)
  have hN : (1 : ℝ) ≤ (i.1.core.card : ℝ) := by exact_mod_cast (core_nonempty i).card_pos
  have hKc : 0 ≤ clusterCost A G c i := by
    unfold clusterCost clusterNearFactor
    positivity
  set dm : ℝ := (siteDiameter i.1.core : ℝ) with hdm
  have hdm0 : 0 ≤ dm := Nat.cast_nonneg _
  set L4 : ℝ := (R.range : ℝ) / (4 * R.params.side) with hL4
  have hL40 : 0 ≤ L4 := by positivity
  have hset := hw.measurableSet_vacant
  have hpm := measurable_truncatedSpinPart st hset h y M i
  refine ⟨fun j => mul_nonneg hKc (coreWeightFrom_pos Y j).le, fun j σ σ' hσ hσ' hd => ?_⟩
  by_cases hji : j = i
  · subst hji
    have e1 : Function.update σ j (σ' j) = σ' := by
      funext k
      by_cases hk : k = j
      · subst hk
        simp
      · rw [Function.update_of_ne hk, hd k hk]
    have hK : gasKernel hw j σ' = gasKernel hw j σ := by
      have := gib.update_eq j σ (σ' j)
      rwa [e1] at this
    have e2 : ∀ s, Function.update σ' j s = Function.update σ j s := fun s => by
      funext k
      by_cases hk : k = j
      · subst hk
        simp
      · rw [Function.update_of_ne hk, Function.update_of_ne hk, hd k hk]
    have : spinAverage (gasKernel hw) (truncatedSpinPart A G h y M j) j σ =
        spinAverage (gasKernel hw) (truncatedSpinPart A G h y M j) j σ' := by
      unfold spinAverage
      rw [hK]
      simp only [e2]
    rw [this, sub_self, abs_zero]
    exact mul_nonneg hKc (coreWeightFrom_pos Y _).le
  have hij : i ≠ j := Ne.symm hji
  obtain ⟨g1, g2⟩ := setGap_singleton_bounds hYc j
  set Gp := setGap i.1.core j.1.core with hGp
  set dj := setGap {Y} j.1.core with hdj
  have g1r : (Gp : ℝ) ≤ dj := by exact_mod_cast g1
  have g2r : (dj : ℝ) ≤ Gp + dm := by
    rw [hdm]
    exact_mod_cast g2
  have hNj : (1 : ℝ) ≤ (j.1.core.card : ℝ) := by exact_mod_cast (core_nonempty j).card_pos
  have hseen : Real.exp (-(columnRate R * (dj : ℝ))) ≤ G.coreWeightFrom Y j := by
    show _ ≤ (j.1.core.card : ℝ) * Real.exp (-(R.params.rt / 2 ^ 6 * (setGap {Y} j.1.core : ℝ)))
    have : columnRate R = R.params.rt / 2 ^ 6 := rfl
    rw [← this, ← hdj]
    nlinarith [Real.exp_pos (-(columnRate R * (dj : ℝ)))]
  have hThr : nearRadius R = (nearGap R.params.side R.range : ℝ) + L4 + 3 := rfl
  have hTh0 : 0 ≤ nearRadius R := by
    rw [hThr]
    positivity
  have hfin : ∀ {Xb : ℝ}, Xb ≤ 20 * (A.responseParams.C₀ + 1) * Real.exp (columnRate R * (nearRadius R + 4)) *
      (G.spinActivity c i * (i.1.core.card : ℝ) * Real.exp (2 * columnRate R * dm)) * Real.exp (-(columnRate R * (dj : ℝ))) →
      Xb ≤ clusterCost A G c i * G.coreWeightFrom Y j := fun hX =>
    hX.trans (mul_le_mul_of_nonneg_left hseen hKc)
  by_cases hc : G.IsNear i j ∨ (Gp : ℝ) ≤ L4 + 3
  · have a1 := st.abs_integral_truncatedSpinPart_le hsz hy hM hz0 (gasKernel hw i σ) σ (hmom σ hσ)
    have a2 := st.abs_integral_truncatedSpinPart_le hsz hy hM hz0 (gasKernel hw i σ') σ' (hmom σ' hσ')
    have hGq : (Gp : ℝ) ≤ nearRadius R := by
      rcases hc with hn | hn
      · have : (Gp : ℝ) ≤ (nearGap R.params.side R.range : ℝ) := by exact_mod_cast setGap_le_nearGap hn
        rw [hThr]
        linarith
      · rw [hThr]
        have : (0 : ℝ) ≤ (nearGap R.params.side R.range : ℝ) := Nat.cast_nonneg _
        linarith
    refine hfin ?_
    have nn := near_bound_arith hC1 hz0 hN hrp.le hdm0 g2r hGq
    refine le_trans ?_ nn
    have : |spinAverage (gasKernel hw) (truncatedSpinPart A G h y M i) i σ -
          spinAverage (gasKernel hw) (truncatedSpinPart A G h y M i) i σ'| ≤
        |spinAverage (gasKernel hw) (truncatedSpinPart A G h y M i) i σ| +
          |spinAverage (gasKernel hw) (truncatedSpinPart A G h y M i) i σ'| := abs_sub _ _
    unfold spinAverage at this ⊢
    linarith
  push Not at hc
  obtain ⟨hnear, hG⟩ := hc
  have hF : G.pairConstraint.AllCompatible i j := fun s t => Or.inr (Or.inr (not_not.mp hnear))
  have hdj2 : 2 ≤ dj := by
    have : (2 : ℝ) ≤ dj := by linarith
    exact_mod_cast this
  have hmr : ((dj - 2 : ℕ) : ℝ) = (dj : ℝ) - 2 := by
    rw [Nat.cast_sub hdj2]
    norm_num
  have hm : L4 ≤ ((dj - 2 : ℕ) : ℝ) := by
    rw [hmr]
    linarith
  set E := Real.exp (-(R.params.rt * ((dj - 2 : ℕ) : ℝ) / 2 ^ 5)) with hE
  set P := gasKernel hw i σ with hPd
  set P' := gasKernel hw i σ' with hP'd
  set g : G.SpinValue i → ℝ := fun s => truncatedSpinPart A G h y M i (Function.update σ i s) with hg
  set g' : G.SpinValue i → ℝ := fun s => truncatedSpinPart A G h y M i (Function.update σ' i s) with hg'
  have hgm : Measurable g := hpm.comp (measurable_update σ)
  have hgm' : Measurable g' := hpm.comp (measurable_update σ')
  have hgb : ∀ s, |g s| ≤ M := fun s => abs_truncatedSpinPart_le hM i _
  have hgb' : ∀ s, |g' s| ≤ M := fun s => abs_truncatedSpinPart_le hM i _
  have hgi : Integrable g P := Integrable.of_bound hgm.aestronglyMeasurable M (Filter.Eventually.of_forall hgb)
  have hgi' : Integrable g' P := Integrable.of_bound hgm'.aestronglyMeasurable M (Filter.Eventually.of_forall hgb')
  have h1 : |∫ s, (g s - g' s) ∂P| ≤ (2 * E) * (3 * G.spinActivity c i) :=
    abs_integral_le_of_lintegral_le P (E := expSpinLabel A G i y) (by positivity) (by positivity)
      (fun s => st.abs_truncatedSpinPart_sub_le hsz hy hM hF hij hσ hσ' hd hm (Nat.sub_add_cancel hdj2).le s) (hmom σ hσ)
  rw [integral_sub hgi hgi'] at h1
  set k : ℝ := A.responseParams.C₀ + columnRate R * ((Gp : ℝ) + dm) with hk
  have hk0 : 0 ≤ k := by positivity
  have hcc : Real.exp (A.responseParams.C₀ - k) = Real.exp (-(columnRate R * ((Gp : ℝ) + dm))) := by
    congr 1
    rw [hk]
    ring
  have hgk : ∀ s, |g' s| - k ≤ Real.exp (-(columnRate R * ((Gp : ℝ) + dm))) * expSpinLabel A G i y s := fun s => by
    have := st.truncatedSpinPart_tail hsz hy hM hk0 (Function.update σ' i s)
    rw [Function.update_self, hcc] at this
    exact this
  have hPP' : IsProbabilityMeasure P := (hmk i).isProbabilityMeasure σ
  have hP'P : IsProbabilityMeasure P' := (hmk i).isProbabilityMeasure σ'
  have h2 := integral_sub_le_of_tail P P' (ε := G.influenceMatrix c i j / 2) (T := 3 * G.spinActivity c i) hk0
    (Real.exp_pos _).le (by positivity)
    (cols.kernel_le i j hij σ σ' hσ hσ' hd) hgm' hgb' (expSpinLabel_nonneg i y) hgk (hmom σ hσ) (hmom σ' hσ')
  have h3 := integral_sub_le_of_tail P' P (ε := G.influenceMatrix c i j / 2) (T := 3 * G.spinActivity c i) hk0
    (Real.exp_pos _).le (by positivity)
    (cols.kernel_le i j hij σ' σ hσ' hσ fun k hk => (hd k hk).symm) hgm' hgb' (expSpinLabel_nonneg i y) hgk (hmom σ' hσ')
    (hmom σ hσ)
  have hEn : E ≤ Real.exp (4 * columnRate R) * Real.exp (-(columnRate R * (dj : ℝ))) := by
    rw [← Real.exp_add, hE, hmr]
    apply Real.exp_le_exp.mpr
    have e2 : R.params.rt = 2 ^ 6 * columnRate R := by unfold columnRate; ring
    rw [e2]
    have : 0 ≤ columnRate R * (dj : ℝ) := by positivity
    nlinarith
  have hεn : 2 * (G.influenceMatrix c i j / 2) ≤
      8 * G.spinActivity c i * ((i.1.core.card : ℝ) * Real.exp (-(8 * columnRate R * (Gp : ℝ)))) := by
    have e0 : G.influenceMatrix c i j = 8 * G.spinActivity c i * min 1 ((i.1.core.card : ℝ) *
        Real.exp (-(R.params.rt * (Gp : ℝ) / 8))) := by
      unfold GasGround.influenceMatrix spinInfluence
      rw [if_neg hnear]
    have e1 : R.params.rt * (Gp : ℝ) / 8 = 8 * columnRate R * (Gp : ℝ) := by
      unfold columnRate
      ring
    rw [e1] at e0
    rw [e0]
    have : min 1 ((i.1.core.card : ℝ) * Real.exp (-(8 * columnRate R * (Gp : ℝ)))) ≤
        (i.1.core.card : ℝ) * Real.exp (-(8 * columnRate R * (Gp : ℝ))) := min_le_right _ _
    have h8 : 0 ≤ 8 * G.spinActivity c i := by positivity
    have := mul_le_mul_of_nonneg_left this h8
    linarith
  have fn := far_bound_arith hC0 hz0 hN hrp.le hdm0 (Nat.cast_nonneg _) hTh0 g2r g1r hEn hεn
  refine hfin (le_trans ?_ fn)
  show |(∫ s, g s ∂P) - ∫ s, g' s ∂P'| ≤ _
  rw [abs_le]
  have a1 := (abs_le.mp h1).1
  have a2 := (abs_le.mp h1).2
  constructor <;> linarith
end Osc
end Oscillation
section Summation
variable {R : StepSetup} {n : ℕ} [NeZero n] {G : GasGround R n}
section Sums
variable {A : ResponseSetup R} {Q : Finset (TorusSite n)} {B : Finset (TorusSite (n * R.params.side))} {e c : ℝ}
  {Yt : G.Config → ℝ} {s : R.labels.Ω → ℝ}
theorem setGap_le_of_mem {Y : TorusSite n} (hY : Y ∈ Q) (i : G.GasSpin) : setGap Q i.1.core ≤ setGap {Y} i.1.core := by apply _root_.YangMills.Construction.TiltedGasResponse.setGap_le_setGap_singleton <;> assumption
theorem tilt_dichotomy (ht : IsGasTilt G s Q B e Yt) (he : 1 ≤ e) (hr8 : 8 * R.params.side ≤ R.range)
    (hz0 : ∀ i, 0 ≤ G.spinActivity c i) (i : G.GasSpin) :
    2 * (G.spinActivity c i + 3 * G.spinActivity c i) ≤ 2 * tiltActivity G c e Q i ∨ ∃ e' : ℝ, 0 ≤ e' ∧ e' ≤ 1 ∧
      8 * e' * G.spinActivity c i ≤ 2 * tiltActivity G c e Q i ∧
      ∀ (σ : G.Config) (v : G.SpinValue i), G.pairConstraint.IsAdmissible (Function.update σ i v) →
        v ≠ G.pairConstraint.vacant i →
        |Yt (Function.update σ i v) - Yt (Function.update σ i (G.pairConstraint.vacant i))| ≤
          e' * Yt (Function.update σ i (G.pairConstraint.vacant i)) := by
  classical
  have hz := hz0 i
  have hL : (0 : ℝ) < R.params.side := by exact_mod_cast Nat.pos_of_ne_zero (NeZero.ne R.params.side)
  unfold tiltActivity
  set l := setGap Q i.1.core with hl
  by_cases h1 : (R.range : ℝ) / (2 * R.params.side) ≤ l
  · rw [if_pos h1]
    set E2 := Real.exp (-(R.params.rt * ((l : ℝ) - 2) / 2 ^ 5)) with hE2
    by_cases h2 : 1 ≤ e * E2
    · left
      have : 1 ≤ min 2 (e * E2) := le_min (by norm_num) h2
      nlinarith
    · right
      have h3 : e * E2 < 1 := not_le.mp h2
      have hmin : min 2 (e * E2) = e * E2 := min_eq_right (by linarith)
      have h4 : (R.range : ℝ) / (2 * R.params.side) ≥ 4 := by
        rw [ge_iff_le, le_div_iff₀ (by positivity)]
        have : (8 * R.params.side : ℝ) ≤ R.range := by exact_mod_cast hr8
        linarith
      have h6 : 2 ≤ l := by
        have : (2 : ℝ) ≤ l := by linarith
        exact_mod_cast this
      have hmr : ((l - 2 : ℕ) : ℝ) = (l : ℝ) - 2 := by
        rw [Nat.cast_sub h6]
        norm_num
      have h7 : (R.range : ℝ) / (4 * R.params.side) ≤ ((l - 2 : ℕ) : ℝ) := by
        have e1 : (R.range : ℝ) / (4 * R.params.side) = (R.range : ℝ) / (2 * R.params.side) / 2 := by
          field_simp
          ring
        rw [hmr, e1]
        linarith
      refine ⟨e * E2, by positivity, h3.le, ?_, fun σ v ha _ => ?_⟩
      · rw [hmin]
        apply le_of_eq
        ring
      · have := ht.abs_update_sub_le σ i v (l - 2) ha h7 fun Y hY => by
          have := setGap_le_of_mem hY i
          omega
        rw [hmr] at this
        exact this
  · left
    rw [if_neg h1]
    nlinarith
theorem le_siteDiameter_add_setGap {Y : TorusSite n} {D : ℕ} (hQ : Q.Nonempty) (hD : ∀ Y' ∈ Q, D ≤ _root_.YangMills.Construction.TorusFields.supDist Y Y')
    {i : G.GasSpin} (hY : Y ∈ i.1.core) :
    D ≤ siteDiameter i.1.core + setGap Q i.1.core := by
  obtain ⟨Y', hY', a', ha', e₂⟩ := exists_supDist_eq_setGap hQ (core_nonempty i)
  have h1 := hD Y' hY'
  have h2 := _root_.YangMills.Construction.TorusFields.supDist_triangle Y a' Y'
  have h4 : _root_.YangMills.Construction.TorusFields.supDist Y a' ≤ siteDiameter i.1.core := by
    unfold siteDiameter
    exact (Finset.le_sup (f := fun z => _root_.YangMills.Construction.TorusFields.supDist Y z) ha').trans
      (Finset.le_sup (f := fun y => i.1.core.sup fun z => _root_.YangMills.Construction.TorusFields.supDist y z) hY)
  rw [_root_.YangMills.Construction.TorusFields.supDist_comm a' Y'] at h2
  omega
def blockSumConstant : ℝ := (2 / (1 - Real.exp (-(1 / 4)))) ^ 4
theorem blockSumConstant_nonneg : 0 ≤ blockSumConstant := Even.pow_nonneg (by decide) _
theorem setGap_singleton_of_mem {i : G.GasSpin} {Y : TorusSite n} (hY : Y ∈ i.1.core) : setGap {Y} i.1.core = 0 := by
  have := setGap_le (Finset.mem_singleton_self Y) hY
  rw [_root_.YangMills.Construction.TorusFields.supDist_self] at this
  omega
theorem sum_le_of_mem_core (hgas : StepGas.GasSumNearBlockBound) (hfit : R.params.Admissible) (hc0 : 0 < c)
    (hcf : R.params.RangeFloor c) (hy : R.params.y₁ ≤ R.coupling) (hrt : 0 < R.params.rt)
    (hz0 : ∀ i, 0 ≤ G.spinActivity c i) (Y : TorusSite n) (S : Finset G.GasSpin)
    (hS : ∀ i ∈ S, Y ∈ i.1.core) {t : G.GasSpin → ℝ} {Cb : ℝ} (hCb : 0 ≤ Cb)
    (ht : ∀ i ∈ S, t i ≤ Cb * (G.spinActivity c i * (i.1.core.card : ℝ) *
      Real.exp (2 * columnRate R * (siteDiameter i.1.core : ℝ)))) :
    ∑ i ∈ S, t i ≤ Cb * Real.exp (-(8 * c * R.coupling)) * blockSumConstant := by
  have hrp : columnRate R ≤ R.params.rt := by
    unfold columnRate
    linarith
  refine hgas R n G c 1 Cb Y S t hfit hc0 hcf hy one_pos hCb fun i hi => ?_
  rw [setGap_singleton_of_mem (hS i hi)]
  have hN : (1 : ℝ) ≤ (i.1.core.card : ℝ) := by exact_mod_cast (core_nonempty i).card_pos
  have hN4 : (i.1.core.card : ℝ) ≤ (i.1.core.card : ℝ) ^ 4 := by
    calc (i.1.core.card : ℝ) = (i.1.core.card : ℝ) ^ 1 := (pow_one _).symm
      _ ≤ _ := pow_le_pow_right₀ hN (by norm_num)
  have hE : Real.exp (2 * columnRate R * (siteDiameter i.1.core : ℝ)) ≤
      Real.exp (2 * R.params.rt * (i.1.coreDiam : ℝ)) := by
    apply Real.exp_le_exp.mpr
    show 2 * columnRate R * (i.1.coreDiam : ℝ) ≤ _
    nlinarith
  have hz := hz0 i
  refine (ht i hi).trans ?_
  simp only [Nat.cast_zero, mul_zero, neg_zero, Real.exp_zero, mul_one]
  gcongr
end Sums
section Dominated
variable {A : ResponseSetup R}
open Classical in
theorem sum_admissibleResponse_eq_classResponsePart (st : FarTiltContext A G)
    (h : PlaquetteWeight (fineSide R.params.side R.depth (n * R.params.side))) (y : TorusSite (n * R.params.side))
    (σ : G.Config) :
    (∑ i ∈ Finset.univ.filter (fun i : G.GasSpin => y ∈ i.1.2),
        if σ i = G.pairConstraint.vacant i then 0 else admissibleResponse A G h y σ) =
      classResponsePart A G y h σ := by
  unfold classResponsePart
  by_cases hσ : G.pairConstraint.IsAdmissible σ
  · have hg : admissibleResponse A G h y σ = chartResponse A (configSetting G σ) y h := by
      unfold admissibleResponse
      rw [if_pos hσ]
      exact st.siteResponse_eq hσ h y
    by_cases hex : ∃ i : G.GasSpin, y ∈ i.1.2 ∧ σ i ≠ G.pairConstraint.vacant i
    · rw [if_pos ⟨hσ, hex⟩, ← hg]
      obtain ⟨i, hi, hp⟩ := hex
      rw [Finset.sum_eq_single i]
      · rw [if_neg hp]
      · intro j hj hji
        have hyj : y ∈ j.1.2 := (Finset.mem_filter.mp hj).2
        rcases hσ i j (Ne.symm hji) with h1 | h1 | h1
        · exact absurd h1 hp
        · exact if_pos h1
        · have := h1 y (Finset.mem_union_right _ hi) y (Finset.mem_union_right _ hyj)
          simp [_root_.YangMills.Construction.TorusFields.supDist_self] at this
      · intro hn
        exact absurd (Finset.mem_filter.mpr ⟨Finset.mem_univ i, hi⟩) hn
    · rw [if_neg fun hh => hex hh.2]
      refine Finset.sum_eq_zero fun i hi => ?_
      by_cases hp : σ i = G.pairConstraint.vacant i
      · rw [if_pos hp]
      · exact absurd ⟨i, (Finset.mem_filter.mp hi).2, hp⟩ hex
  · have hg : admissibleResponse A G h y σ = 0 := by
      unfold admissibleResponse
      rw [if_neg hσ]
    rw [if_neg fun hh => hσ hh.1, hg]
    exact Finset.sum_eq_zero fun i _ => by simp
theorem integrable_expSpinLabel (hP : Dobrushin.MeanOfProductStatement) {W : G.Config → ℝ} {z : G.GasSpin → ℝ}
    (hW : G.pairConstraint.IsActivityBounded (G.referenceMeasure ∅) W z)
    [IsProbabilityMeasure (G.pairConstraint.gibbsLaw (G.referenceMeasure ∅) W)]
    (hb : Measurable A.score) (i : G.GasSpin) (y : TorusSite (n * R.params.side)) {T : ℝ} (hT : 0 ≤ T)
    (hex : ∀ σ, G.pairConstraint.IsAdmissible σ → ∫⁻ s in {G.pairConstraint.vacant i}ᶜ,
      ENNReal.ofReal (expSpinLabel A G i y s) *
        G.pairConstraint.weightDensity W (Function.update σ i s) ∂(G.referenceMeasure ∅ i) ≤
        ENNReal.ofReal T * G.pairConstraint.weightDensity W (Function.update σ i (G.pairConstraint.vacant i))) :
    Integrable (fun σ : G.Config => expSpinLabel A G i y (σ i)) (G.pairConstraint.gibbsLaw (G.referenceMeasure ∅) W) := by
  have hm := measurable_expSpinLabel (A := A) (G := G) hb i (hW.measurableSet_vacant i) y
  have h1 := lintegral_gibbsLaw_single_le hP G.pairConstraint (G.referenceMeasure ∅) hW i hm (expSpinLabel_nonneg i y)
    (expSpinLabel_vacant i y) hT hex
  refine ⟨(hm.comp (measurable_pi_apply i)).aestronglyMeasurable, ?_⟩
  rw [hasFiniteIntegral_iff_ofReal (Filter.Eventually.of_forall fun σ => expSpinLabel_nonneg i y _)]
  exact lt_of_le_of_lt h1 ENNReal.ofReal_lt_top
open Classical in
theorem classResponsePart_limit (st : FarTiltContext A G)
    (hset : ∀ i, MeasurableSet ({G.pairConstraint.vacant i} : Set (G.SpinValue i)))
    {h : PlaquetteWeight (fineSide R.params.side R.depth (n * R.params.side))} (hsz : weightNorm R.params.side R.depth h ≤ 1)
    {y : TorusSite (n * R.params.side)} (ν μ : Measure G.Config)
    (hν : ∀ i : G.GasSpin, Integrable (fun σ : G.Config => expSpinLabel A G i y (σ i)) ν)
    (hμ : ∀ i : G.GasSpin, Integrable (fun σ : G.Config => expSpinLabel A G i y (σ i)) μ) {T : ℝ}
    (hbd : ∀ N : ℕ, |(∫ σ, ∑ i ∈ Finset.univ.filter (fun i : G.GasSpin => y ∈ i.1.2), truncatedSpinPart A G h y N i σ ∂ν) -
      ∫ σ, ∑ i ∈ Finset.univ.filter (fun i : G.GasSpin => y ∈ i.1.2), truncatedSpinPart A G h y N i σ ∂μ| ≤ T) :
    Integrable (classResponsePart A G y h) ν ∧ Integrable (classResponsePart A G y h) μ ∧
      |∫ σ, classResponsePart A G y h σ ∂ν - ∫ σ, classResponsePart A G y h σ ∂μ| ≤ T := by
  set S := Finset.univ.filter (fun i : G.GasSpin => y ∈ i.1.2) with hS
  set bound : G.Config → ℝ := fun σ => ∑ i ∈ S, (A.responseParams.C₀ + 1) * expSpinLabel A G i y (σ i) with hbound
  have hFm : ∀ N : ℕ, Measurable fun σ => ∑ i ∈ S, truncatedSpinPart A G h y N i σ := fun N =>
    Finset.measurable_fun_sum _ fun i _ => measurable_truncatedSpinPart st hset h y N i
  have hbF : ∀ (N : ℕ) σ, ‖∑ i ∈ S, truncatedSpinPart A G h y N i σ‖ ≤ bound σ := fun N σ => by
    rw [Real.norm_eq_abs]
    refine (Finset.abs_sum_le_sum_abs _ _).trans (Finset.sum_le_sum fun i hi => ?_)
    exact st.abs_truncatedSpinPart_le_exp hsz (Finset.mem_filter.mp hi).2 (Nat.cast_nonneg N) σ
  have hlim : ∀ σ, Filter.Tendsto (fun N : ℕ => ∑ i ∈ S, truncatedSpinPart A G h y N i σ) Filter.atTop
      (nhds (classResponsePart A G y h σ)) := fun σ => by
    rw [← sum_admissibleResponse_eq_classResponsePart st h y σ]
    refine tendsto_const_nhds.congr' ?_
    obtain ⟨N₀, hN₀⟩ := exists_nat_ge |admissibleResponse A G h y σ|
    filter_upwards [Filter.eventually_ge_atTop N₀] with N hN
    refine Finset.sum_congr rfl fun i _ => ?_
    unfold truncatedSpinPart
    by_cases hp : σ i = G.pairConstraint.vacant i
    · rw [if_pos hp, if_pos hp]
    · rw [if_neg hp, if_neg hp, truncateAt_eq_self]
      exact hN₀.trans (by exact_mod_cast hN)
  have hcm : Measurable (classResponsePart A G y h) := measurable_of_tendsto_metrizable hFm (tendsto_pi_nhds.mpr hlim)
  have hbc : ∀ σ, ‖classResponsePart A G y h σ‖ ≤ bound σ := fun σ =>
    le_of_tendsto (tendsto_norm.comp (hlim σ)) (Filter.Eventually.of_forall fun N => hbF N σ)
  have hbi : ∀ (L : Measure G.Config), (∀ i : G.GasSpin, Integrable (fun σ : G.Config => expSpinLabel A G i y (σ i)) L) →
      Integrable bound L := fun L hL =>
    integrable_finsetSum _ fun i _ => (hL i).const_mul _
  have int1 : ∀ (L : Measure G.Config), Integrable bound L → Integrable (classResponsePart A G y h) L := fun L hL =>
    hL.mono' hcm.aestronglyMeasurable (Filter.Eventually.of_forall hbc)
  have hb1 := hbi ν hν
  have hb2 := hbi μ hμ
  refine ⟨int1 ν hb1, int1 μ hb2, ?_⟩
  have t1 := tendsto_integral_of_dominated_convergence (μ := ν) bound (fun N => (hFm N).aestronglyMeasurable) hb1
    (fun N => Filter.Eventually.of_forall (hbF N)) (Filter.Eventually.of_forall hlim)
  have t2 := tendsto_integral_of_dominated_convergence (μ := μ) bound (fun N => (hFm N).aestronglyMeasurable) hb2
    (fun N => Filter.Eventually.of_forall (hbF N)) (Filter.Eventually.of_forall hlim)
  exact le_of_tendsto ((t1.sub t2).abs) (Filter.Eventually.of_forall hbd)
end Dominated
end Summation
section RestBounds
variable {R : StepSetup} {n : ℕ} [NeZero n] {G : GasGround R n}
section Core
variable {A : ResponseSetup R} {Q : Finset (TorusSite n)} {B : Finset (TorusSite (n * R.params.side))} {e c : ℝ}
  {Yt : G.Config → ℝ}
theorem final_bound_arith {C1 e q Bb Bn W Ci cx rD : ℝ} (hC1 : 0 ≤ C1) (he : 1 ≤ e) (hq : 1 ≤ q) (hBb : 1 ≤ Bb)
    (hBn : 1 ≤ Bn) (hW : 0 ≤ W) (hCi : 0 ≤ Ci) (hcx : 0 ≤ cx) (hrD : 0 ≤ rD) (h : Bb * Bn * Real.exp (-cx) ≤ 1) :
    (9 * C1 * e * Bb * Real.exp (-(2 * rD))) * Real.exp (-(8 * cx)) * W +
        (20 * C1 * Bn * Real.exp (-(8 * cx)) * W) * (2 * (2 * (Ci * e * q * Real.exp (-(7 * cx) - rD)))) ≤
      (9 + 80 * Ci) * C1 * W * e * q * Real.exp (-(6 * cx) - rD) := by
  have hE : Real.exp (-cx) * Real.exp cx = 1 := by rw [← Real.exp_add]; simp
  have hEp := Real.exp_pos cx
  have h1 : Bb * Bn ≤ Real.exp cx := by
    have : Bb * Bn * Real.exp (-cx) * Real.exp cx ≤ 1 * Real.exp cx := mul_le_mul_of_nonneg_right h hEp.le
    rw [mul_assoc, hE] at this
    linarith
  have hBbE : Bb ≤ Real.exp cx := by nlinarith
  have hBnE : Bn ≤ Real.exp cx := by nlinarith
  have a1 : Bb * Real.exp (-(8 * cx)) ≤ Real.exp (-(6 * cx)) := by
    calc _ ≤ Real.exp cx * Real.exp (-(8 * cx)) := by gcongr
      _ = Real.exp (-(7 * cx)) := by rw [← Real.exp_add]; congr 1; ring
      _ ≤ _ := Real.exp_le_exp.mpr (by linarith)
  have a2 : Bn * Real.exp (-(8 * cx)) ≤ 1 := by
    calc _ ≤ Real.exp cx * Real.exp (-(8 * cx)) := by gcongr
      _ = Real.exp (-(7 * cx)) := by rw [← Real.exp_add]; congr 1; ring
      _ ≤ 1 := Real.exp_le_one_iff.mpr (by linarith)
  have a3 : Real.exp (-(2 * rD)) ≤ Real.exp (-rD) := Real.exp_le_exp.mpr (by linarith)
  have a4 : Real.exp (-(7 * cx) - rD) ≤ Real.exp (-(6 * cx) - rD) := Real.exp_le_exp.mpr (by linarith)
  have hX : Real.exp (-(6 * cx)) * Real.exp (-rD) = Real.exp (-(6 * cx) - rD) := by
    rw [← Real.exp_add]
    congr 1
  have t1 : (9 * C1 * e * Bb * Real.exp (-(2 * rD))) * Real.exp (-(8 * cx)) * W ≤
      9 * C1 * W * e * q * Real.exp (-(6 * cx) - rD) := by
    calc _ = 9 * C1 * W * e * (Bb * Real.exp (-(8 * cx))) * Real.exp (-(2 * rD)) := by ring
      _ ≤ 9 * C1 * W * e * Real.exp (-(6 * cx)) * Real.exp (-rD) := by gcongr
      _ = 9 * C1 * W * e * 1 * Real.exp (-(6 * cx) - rD) := by rw [← hX]; ring
      _ ≤ _ := by gcongr
  have t2 : (20 * C1 * Bn * Real.exp (-(8 * cx)) * W) * (2 * (2 * (Ci * e * q * Real.exp (-(7 * cx) - rD)))) ≤
      80 * Ci * C1 * W * e * q * Real.exp (-(6 * cx) - rD) := by
    calc _ = 80 * Ci * C1 * W * e * q * (Bn * Real.exp (-(8 * cx))) * Real.exp (-(7 * cx) - rD) := by ring
      _ ≤ 80 * Ci * C1 * W * e * q * 1 * Real.exp (-(6 * cx) - rD) := by gcongr
      _ = _ := by ring
  calc _ ≤ 9 * C1 * W * e * q * Real.exp (-(6 * cx) - rD) + 80 * Ci * C1 * W * e * q * Real.exp (-(6 * cx) - rD) :=
        add_le_add t1 t2
    _ = _ := by ring
theorem FarTiltContext.abs_spinAverage_sub_le (st : FarTiltContext A G)
    {h : PlaquetteWeight (fineSide R.params.side R.depth (n * R.params.side))} (hsz : weightNorm R.params.side R.depth h ≤ 1)
    {y : TorusSite (n * R.params.side)} {i : G.GasSpin} (hy : y ∈ i.1.2) {M : ℝ} (hM : 0 ≤ M) (he : 1 ≤ e)
    (hrt : 0 < R.params.rt)
    (ht : IsGasTilt G A.score Q B e Yt) {z z' : G.GasSpin → ℝ}
    (hw : G.pairConstraint.IsActivityBounded (G.referenceMeasure ∅) G.weight z)
    (hw' : G.pairConstraint.IsActivityBounded (G.referenceMeasure ∅) (fun σ => G.weight σ * Yt σ) z')
    (gib : G.pairConstraint.IsSpecification (G.pairConstraint.gibbsLaw (G.referenceMeasure ∅) G.weight) (gasKernel hw))
    (hz : z i ≤ 1 / 2) (hz0 : 0 ≤ z i)
    (hpres : ∀ σ, G.pairConstraint.IsAdmissible σ → (gasKernel hw i σ).real {G.pairConstraint.vacant i}ᶜ ≤ z i)
    [IsMarkovKernel (gasKernel hw' i)] {σ : G.Config} (hσ : G.pairConstraint.IsAdmissible σ)
    (hmom : ∫⁻ s, ENNReal.ofReal (expSpinLabel A G i y s) ∂(gasKernel hw i σ) ≤ ENNReal.ofReal (3 * z i))
    (hmom' : ∫⁻ s, ENNReal.ofReal (expSpinLabel A G i y s) ∂(gasKernel hw' i σ) ≤ ENNReal.ofReal (3 * z i)) :
    |spinAverage (gasKernel hw') (truncatedSpinPart A G h y M i) i σ -
        spinAverage (gasKernel hw) (truncatedSpinPart A G h y M i) i σ| ≤
      3 * (e * (tiltNearFactor R * Real.exp (-(2 * columnRate R * (setGap Q i.1.core : ℝ))))) *
        ((A.responseParams.C₀ + 1) * (3 * z i)) := by
  classical
  set l := setGap Q i.1.core with hl
  set m := l - 2 with hm
  set L4 : ℝ := (R.range : ℝ) / (4 * R.params.side) with hL4
  have hL40 : 0 ≤ L4 := by positivity
  have hrp : 0 < columnRate R := by unfold columnRate; positivity
  have hC1 : 0 ≤ A.responseParams.C₀ + 1 := by linarith [st.C₀_nonneg]
  have hX0 : 0 ≤ (A.responseParams.C₀ + 1) * (3 * z i) := by positivity
  set U := tiltNearFactor R * Real.exp (-(2 * columnRate R * (l : ℝ))) with hU
  have hBb0 : 0 ≤ tiltNearFactor R := (Real.exp_pos _).le
  have hU0 : 0 ≤ U := mul_nonneg hBb0 (Real.exp_pos _).le
  have hmk : IsMarkovKernel (gasKernel hw i) := gib.isMarkovKernel i
  by_cases hc : 2 ≤ l ∧ L4 ≤ m
  · obtain ⟨h2, hmr⟩ := hc
    have hEU : Real.exp (-(R.params.rt * m / 2 ^ 5)) ≤ U := by
      rw [hU]
      unfold tiltNearFactor
      rw [← Real.exp_add]
      apply Real.exp_le_exp.mpr
      have e1 : (l : ℝ) = m + 2 := by
        have : l = m + 2 := by omega
        rw [this]
        push_cast
        ring
      have e2 : R.params.rt = 2 ^ 6 * columnRate R := by unfold columnRate; ring
      rw [e1, e2]
      have : 0 ≤ columnRate R * L4 := by positivity
      nlinarith
    have he0 : 0 ≤ e := by linarith
    have := st.abs_spinAverage_tilt_sub_le hsz hy hM hw hw' gib ht.measurable ht.pos hz hz0 hpres hσ hmom
      (e' := e * Real.exp (-(R.params.rt * m / 2 ^ 5))) (by positivity) fun v _ ha =>
        ht.abs_update_sub_le σ i v m ha hmr fun Y hY => by
          have := setGap_le_of_mem hY i
          omega
    refine this.trans ?_
    gcongr
  · have h3 : (l : ℝ) ≤ L4 + 3 := by
      by_cases h5 : 2 ≤ l
      · have h6 : (m : ℝ) < L4 := by
          by_contra hn
          exact hc ⟨h5, not_lt.mp hn⟩
        have e1 : (l : ℝ) = m + 2 := by
          have : l = m + 2 := by omega
          rw [this]
          push_cast
          ring
        linarith
      · have : (l : ℝ) ≤ 2 := by
          have : l ≤ 2 := by omega
          exact_mod_cast this
        linarith
    have h4 : 1 ≤ U := by
      rw [hU]
      unfold tiltNearFactor
      rw [← Real.exp_add]
      apply Real.one_le_exp
      nlinarith
    have h5 : 1 ≤ e * U := by nlinarith
    have b1 := st.abs_integral_truncatedSpinPart_le hsz hy hM hz0 (gasKernel hw' i σ) σ hmom'
    have b2 := st.abs_integral_truncatedSpinPart_le hsz hy hM hz0 (gasKernel hw i σ) σ hmom
    have : |spinAverage (gasKernel hw') (truncatedSpinPart A G h y M i) i σ -
          spinAverage (gasKernel hw) (truncatedSpinPart A G h y M i) i σ| ≤
        |spinAverage (gasKernel hw') (truncatedSpinPart A G h y M i) i σ| +
          |spinAverage (gasKernel hw) (truncatedSpinPart A G h y M i) i σ| := abs_sub _ _
    unfold spinAverage at this ⊢
    nlinarith
end Core
end RestBounds
section Closing
variable {R : StepSetup} {n : ℕ} [NeZero n] {G : GasGround R n}
section Close
variable {A : ResponseSetup R} {Q : Finset (TorusSite n)} {B : Finset (TorusSite (n * R.params.side))} {e c : ℝ}
  {Yt : G.Config → ℝ}
theorem tiltActivity_nonneg {i : G.GasSpin} (hz : 0 ≤ G.spinActivity c i) (he : 0 ≤ e) : 0 ≤ tiltActivity G c e Q i := by
  classical
  unfold tiltActivity
  split_ifs
  · have : 0 ≤ min 2 (e * Real.exp (-(R.params.rt * ((setGap Q i.1.core : ℝ) - 2) / 2 ^ 5))) :=
      le_min (by norm_num) (by positivity)
    positivity
  · positivity
theorem classResponsePart_bound (hT : LinearResponse.TiltedGibbsComparison) (hP : Dobrushin.MeanOfProductStatement)
    (hgas : StepGas.GasSumNearBlockBound) (hC : Dobrushin.ActivityConditionalLawsStatement) (st : FarTiltContext A G)
    (hc0 : 0 < c) (hcf : R.params.RangeFloor c) (hy₁ : R.params.y₁ ≤ R.coupling) (hrt : 0 < R.params.rt) (he : 1 ≤ e)
    (hr8 : 8 * R.params.side ≤ R.range) (hx : 0 ≤ R.coupling)
    (hw : G.pairConstraint.IsActivityBounded (G.referenceMeasure ∅) G.weight (G.spinActivity c))
    (cols : G.HasSmallColumns (fun j => j.1.Touches ∅) c hw)
    (paid : ∀ (i : G.GasSpin) (σ : G.Config), G.pairConstraint.IsAdmissible σ →
      ∫⁻ v in {G.pairConstraint.vacant i}ᶜ, ENNReal.ofReal (Real.exp (WeightedResponses.spinScore A i v)) *
        G.pairConstraint.weightDensity G.weight (Function.update σ i v) ∂(G.referenceMeasure ∅ i) ≤
      ENNReal.ofReal (G.spinActivity c i) * G.pairConstraint.weightDensity G.weight (Function.update σ i (G.pairConstraint.vacant i)))
    (ht : IsGasTilt G A.score Q B e Yt) (hz2 : ∀ i, G.spinActivity c i ≤ 1 / 2)
    (hfloor : tiltNearFactor R * clusterNearFactor R * Real.exp (-(c * R.coupling)) ≤ 1) {Ci : ℝ} (hCi : 0 ≤ Ci)
    {h : PlaquetteWeight (fineSide R.params.side R.depth (n * R.params.side))} (hsz : weightNorm R.params.side R.depth h ≤ 1)
    {y : TorusSite (n * R.params.side)} (hyB : y ∉ B)
    {D : ℕ} (hQ : Q.Nonempty) (hD : ∀ Y' ∈ Q, D ≤ _root_.YangMills.Construction.TorusFields.supDist (parentBlock R.params.side y) Y')
    (hinf : ∑ i : G.GasSpin, decayFromSet G {parentBlock R.params.side y} i * tiltActivity G c e Q i ≤
      Ci * e * (Q.card : ℝ) * Real.exp (-(7 * c * R.coupling) - R.params.rt / 2 ^ 6 * D)) :
    Integrable (classResponsePart A G y h) (tiltedGibbsLaw G Yt) ∧ Integrable (classResponsePart A G y h) (G.gibbsLaw ∅) ∧
      |∫ σ, classResponsePart A G y h σ ∂(tiltedGibbsLaw G Yt) - G.expectation ∅ (classResponsePart A G y h)| ≤
        ((9 + 80 * Ci) * (A.responseParams.C₀ + 1) * blockSumConstant) * e * (Q.card : ℝ) *
          Real.exp (-(6 * c * R.coupling) - R.params.rt * D / 2 ^ 6) := by
  classical
  have hs := st.response.price.nonneg
  have hbA := st.response.price.borel
  have hz0 := hw.activity_nonneg
  have hzle : ∀ i, G.spinActivity c i ≤ 1 := fun i => (hz2 i).trans (by norm_num)
  have e0 : (0 : ℝ) ≤ e := by linarith
  have hw' := isActivityBounded_tilt hs hw paid ht
  obtain ⟨p1, g1, -, -⟩ := hC G.GasSpin G.SpinValue G.pairConstraint (G.referenceMeasure ∅) _ _ hw'
  obtain ⟨p2, g2, pr2, -⟩ := hC G.GasSpin G.SpinValue G.pairConstraint (G.referenceMeasure ∅) _ _ hw
  have i1 : IsProbabilityMeasure (tiltedGibbsLaw G Yt) := p1
  have i2 : IsProbabilityMeasure (G.gibbsLaw ∅) := p2
  have hmk : ∀ i, IsMarkovKernel (gasKernel hw i) := g2.isMarkovKernel
  have hmk' : ∀ i, IsMarkovKernel (gasKernel hw' i) := g1.isMarkovKernel
  have hset := hw.measurableSet_vacant
  have hC0 := st.C₀_nonneg
  have hC1 : 0 ≤ A.responseParams.C₀ + 1 := by linarith
  set Y := parentBlock R.params.side y with hYd
  set S := Finset.univ.filter (fun i : G.GasSpin => y ∈ i.1.2) with hSd
  have hSY : ∀ i ∈ S, Y ∈ i.1.core := fun i hi =>
    GasSupport.parentBlock_mem_core (Finset.mem_union_right _ (Finset.mem_filter.mp hi).2)
  have hexpM : ∀ i, Measurable (expSpinLabel A G i y) := fun i => measurable_expSpinLabel hbA i (hset i) y
  have hψν : ∀ (i : G.GasSpin) (v : G.SpinValue i),
      expSpinLabel A G i y v * Real.exp (∑ y' ∈ B, spinLabelScore A.score G i y' v) ≤
        1 * Real.exp (WeightedResponses.spinScore A i v) := fun i v => by
    unfold expSpinLabel
    split_ifs
    · rw [zero_mul, one_mul]
      exact (Real.exp_pos _).le
    · rw [one_mul, ← Real.exp_add]
      apply Real.exp_le_exp.mpr
      have := sum_spinLabelScore_le_spinScore hs (insert y B) i v
      rwa [Finset.sum_insert hyB] at this
  have hψμ : ∀ (i : G.GasSpin) (v : G.SpinValue i),
      expSpinLabel A G i y v ≤ 3 * Real.exp (WeightedResponses.spinScore A i v) := fun i v => by
    have hE := Real.exp_pos (WeightedResponses.spinScore A i v)
    unfold expSpinLabel
    split_ifs
    · positivity
    · have h1 := sum_spinLabelScore_le_spinScore hs {y} i v
      rw [Finset.sum_singleton] at h1
      have h2 := Real.exp_le_exp.mpr h1
      linarith
  have hmassμ : ∀ (i : G.GasSpin) (σ : G.Config), G.pairConstraint.IsAdmissible σ →
      ∫⁻ s in {G.pairConstraint.vacant i}ᶜ, ENNReal.ofReal (expSpinLabel A G i y s) *
        G.pairConstraint.weightDensity G.weight (Function.update σ i s) ∂(G.referenceMeasure ∅ i) ≤
      ENNReal.ofReal (3 * G.spinActivity c i) *
        G.pairConstraint.weightDensity G.weight (Function.update σ i (G.pairConstraint.vacant i)) :=
    fun i σ hσ => lintegral_weightDensity_le (by norm_num) (paid i) (hψμ i) hσ
  have hmassν : ∀ (i : G.GasSpin) (σ : G.Config), G.pairConstraint.IsAdmissible σ →
      ∫⁻ s in {G.pairConstraint.vacant i}ᶜ, ENNReal.ofReal (expSpinLabel A G i y s) *
        G.pairConstraint.weightDensity (fun σ => G.weight σ * Yt σ) (Function.update σ i s) ∂(G.referenceMeasure ∅ i) ≤
      ENNReal.ofReal (3 * G.spinActivity c i) *
        G.pairConstraint.weightDensity (fun σ => G.weight σ * Yt σ) (Function.update σ i (G.pairConstraint.vacant i)) :=
    fun i σ hσ => by
      have := lintegral_tilted_weightDensity_le hs hw paid ht i zero_le_one (expSpinLabel_nonneg i y) (hψν i) hσ
      rwa [mul_one] at this
  have hmμ : ∀ (i : G.GasSpin) (σ : G.Config), G.pairConstraint.IsAdmissible σ →
      ∫⁻ s, ENNReal.ofReal (expSpinLabel A G i y s) ∂(gasKernel hw i σ) ≤ ENNReal.ofReal (3 * G.spinActivity c i) :=
    fun i σ hσ =>
      lintegral_singleSiteKernel_le G.pairConstraint (G.referenceMeasure ∅) hw i hσ (hexpM i) (expSpinLabel_vacant i y)
        (hmassμ i σ hσ)
  have hmν : ∀ (i : G.GasSpin) (σ : G.Config), G.pairConstraint.IsAdmissible σ →
      ∫⁻ s, ENNReal.ofReal (expSpinLabel A G i y s) ∂(gasKernel hw' i σ) ≤ ENNReal.ofReal (3 * G.spinActivity c i) :=
    fun i σ hσ =>
      lintegral_singleSiteKernel_le G.pairConstraint (G.referenceMeasure ∅) hw' i hσ (hexpM i) (expSpinLabel_vacant i y)
        (hmassν i σ hσ)
  have hIν : ∀ i : G.GasSpin, Integrable (fun σ : G.Config => expSpinLabel A G i y (σ i)) (tiltedGibbsLaw G Yt) := fun i =>
    integrable_expSpinLabel hP hw' hbA i y (by have := hz0 i; positivity) (hmassν i)
  have hIμ : ∀ i : G.GasSpin, Integrable (fun σ : G.Config => expSpinLabel A G i y (σ i)) (G.gibbsLaw ∅) := fun i =>
    integrable_expSpinLabel hP hw hbA i y (by have := hz0 i; positivity) (hmassμ i)
  have hrp : 0 < columnRate R := by unfold columnRate; positivity
  have hb0 : ∀ i, 0 ≤ 2 * tiltActivity G c e Q i := fun i => by
    have := tiltActivity_nonneg (Q := Q) (hz0 i) e0
    linarith
  obtain ⟨a, ha0, hsum, hcmp⟩ := hT G.GasSpin G.SpinValue G.pairConstraint (G.referenceMeasure ∅) G.weight Yt
    (G.spinActivity c) (fun i => 3 * G.spinActivity c i) hw hw' (G.influenceMatrix c) (fun i => 2 * tiltActivity G c e Q i)
    (G.coreWeightFrom Y) ht.pos hzle cols.influenceMatrix_nonneg hb0 (coreWeightFrom_pos Y) cols.kernel_le
    (fun j => by
      have h1 := cols.column_le Y j
      have h2 := cols.exp_le_half
      have h3 := coreWeightFrom_pos Y j
      calc _ ≤ _ := h1
        _ ≤ G.coreWeightFrom Y j * (1 / 2) := mul_le_mul_of_nonneg_left h2 h3.le
        _ = _ := by ring)
    (fun i => tilt_dichotomy ht he hr8 hz0 i)
  have hseq : ∀ j, G.coreWeightFrom Y j = decayFromSet G {Y} j := fun j => rfl
  set Ii : ℝ := Ci * e * (Q.card : ℝ) * Real.exp (-(7 * c * R.coupling) - R.params.rt / 2 ^ 6 * D) with hIi
  have hI0 : 0 ≤ Ii := by
    have : (0 : ℝ) ≤ (Q.card : ℝ) := Nat.cast_nonneg _
    positivity
  have hasum : ∑ j, G.coreWeightFrom Y j * a j ≤ 2 * (2 * Ii) := by
    refine hsum.trans ?_
    have : ∑ j, G.coreWeightFrom Y j * (2 * tiltActivity G c e Q j) =
        2 * ∑ j, decayFromSet G {Y} j * tiltActivity G c e Q j := by
      rw [Finset.mul_sum]
      refine Finset.sum_congr rfl fun j _ => ?_
      rw [hseq]
      ring
    rw [this]
    linarith
  set Ai : G.GasSpin → ℝ := fun i => 3 * (e * (tiltNearFactor R * Real.exp (-(2 * columnRate R * (setGap Q i.1.core : ℝ))))) *
    ((A.responseParams.C₀ + 1) * (3 * G.spinActivity c i)) with hAi
  have hone : ∀ i ∈ S, ∀ M : ℝ, 0 ≤ M →
      |∫ σ, truncatedSpinPart A G h y M i σ ∂(tiltedGibbsLaw G Yt) - ∫ σ, truncatedSpinPart A G h y M i σ ∂(G.gibbsLaw ∅)| ≤
        Ai i + clusterCost A G c i * (2 * (2 * Ii)) := by
    intro i hi M hM
    have hy : y ∈ i.1.2 := (Finset.mem_filter.mp hi).2
    have hΦm := measurable_truncatedSpinPart st hset h y M i
    have hΦb : ∀ σ, |truncatedSpinPart A G h y M i σ| ≤ M := abs_truncatedSpinPart_le hM i
    have eν := g1.integral_eq i _ hΦm ⟨M, hΦb⟩
    have eμ := g2.integral_eq i _ hΦm ⟨M, hΦb⟩
    have hmk1 := hmk i
    have hmk2 := hmk' i
    have hkνm := measurable_spinAverage (gasKernel hw') i hΦm
    have hkμm := measurable_spinAverage (gasKernel hw) i hΦm
    have hkνb := abs_spinAverage_le (gasKernel hw') i hΦb
    have hkμb := abs_spinAverage_le (gasKernel hw) i hΦb
    have hint : ∀ {k : G.Config → ℝ} (L : Measure G.Config) [IsProbabilityMeasure L], Measurable k → (∀ σ, |k σ| ≤ M) →
        Integrable k L := fun L _ hk hb =>
      Integrable.of_bound hk.aestronglyMeasurable M (Filter.Eventually.of_forall fun σ => by
        rw [Real.norm_eq_abs]
        exact hb σ)
    have hA : |∫ σ, (spinAverage (gasKernel hw') (truncatedSpinPart A G h y M i) i σ -
          spinAverage (gasKernel hw) (truncatedSpinPart A G h y M i) i σ) ∂(tiltedGibbsLaw G Yt)| ≤ Ai i := by
      have := norm_integral_le_of_norm_le_const (μ := tiltedGibbsLaw G Yt) (C := Ai i)
        (f := fun σ => spinAverage (gasKernel hw') (truncatedSpinPart A G h y M i) i σ -
          spinAverage (gasKernel hw) (truncatedSpinPart A G h y M i) i σ) (by
          filter_upwards [g1.ae_admissible] with σ hσ
          rw [Real.norm_eq_abs]
          exact st.abs_spinAverage_sub_le hsz hy hM he hrt ht hw hw' g2 (hz2 i) (hz0 i) (fun σ hσ => pr2 i σ hσ) hσ
            (hmμ i σ hσ) (hmν i σ hσ))
      simpa [Real.norm_eq_abs] using this
    rw [integral_sub (hint _ hkνm hkνb) (hint _ hkμm hkμb)] at hA
    have hosc := st.oscillationBound_spinAverage hsz hy hM hrt hw cols g2 (hmμ i)
    have hB := hcmp _ _ hkμm ⟨M, hkμb⟩ hosc
    have hB' : |∫ σ, spinAverage (gasKernel hw) (truncatedSpinPart A G h y M i) i σ ∂(G.gibbsLaw ∅) -
        ∫ σ, spinAverage (gasKernel hw) (truncatedSpinPart A G h y M i) i σ ∂(tiltedGibbsLaw G Yt)| ≤
          clusterCost A G c i * (2 * (2 * Ii)) := by
      refine hB.trans ?_
      have hK0 : 0 ≤ clusterCost A G c i := by
        unfold clusterCost clusterNearFactor
        have := hz0 i
        positivity
      calc ∑ j, a j * (clusterCost A G c i * G.coreWeightFrom Y j)
          = clusterCost A G c i * ∑ j, G.coreWeightFrom Y j * a j := by
            rw [Finset.mul_sum]
            exact Finset.sum_congr rfl fun j _ => by ring
        _ ≤ _ := mul_le_mul_of_nonneg_left hasum hK0
    have e1 : ∫ σ, truncatedSpinPart A G h y M i σ ∂(tiltedGibbsLaw G Yt) =
        ∫ σ, spinAverage (gasKernel hw') (truncatedSpinPart A G h y M i) i σ ∂(tiltedGibbsLaw G Yt) := eν
    have e2 : ∫ σ, truncatedSpinPart A G h y M i σ ∂(G.gibbsLaw ∅) =
        ∫ σ, spinAverage (gasKernel hw) (truncatedSpinPart A G h y M i) i σ ∂(G.gibbsLaw ∅) := eμ
    rw [e1, e2]
    rw [abs_le] at hA hB' ⊢
    constructor <;> linarith [hA.1, hA.2, hB'.1, hB'.2]
  have hfit := st.params_admissible
  set E8 := Real.exp (-(8 * c * R.coupling)) with hE8
  set rD : ℝ := columnRate R * (D : ℝ) with hrD
  have hrD0 : 0 ≤ rD := by positivity
  have hBb1 : 1 ≤ tiltNearFactor R := by
    unfold tiltNearFactor
    exact Real.one_le_exp (by positivity)
  have hBn1 : 1 ≤ clusterNearFactor R := by
    unfold clusterNearFactor nearRadius
    exact Real.one_le_exp (by positivity)
  have hAsum : ∑ i ∈ S, Ai i ≤
      (9 * (A.responseParams.C₀ + 1) * e * tiltNearFactor R * Real.exp (-(2 * rD))) * E8 * blockSumConstant := by
    refine sum_le_of_mem_core hgas hfit hc0 hcf hy₁ hrt hz0 Y S hSY (by positivity) fun i hi => ?_
    have hN : (1 : ℝ) ≤ (i.1.core.card : ℝ) := by exact_mod_cast (core_nonempty i).card_pos
    have hg := le_siteDiameter_add_setGap hQ hD (hSY i hi)
    have hg' : (D : ℝ) ≤ (siteDiameter i.1.core : ℝ) + (setGap Q i.1.core : ℝ) := by exact_mod_cast hg
    have hz := hz0 i
    have h1 : Real.exp (-(2 * columnRate R * (setGap Q i.1.core : ℝ))) ≤
        Real.exp (-(2 * rD)) * Real.exp (2 * columnRate R * (siteDiameter i.1.core : ℝ)) := by
      rw [← Real.exp_add]
      apply Real.exp_le_exp.mpr
      rw [hrD]
      nlinarith
    have hBb0 : 0 ≤ tiltNearFactor R := by linarith
    have hE := Real.exp_pos (2 * columnRate R * (siteDiameter i.1.core : ℝ))
    have hE' := Real.exp_pos (-(2 * rD))
    simp only [hAi]
    calc 3 * (e * (tiltNearFactor R * Real.exp (-(2 * columnRate R * (setGap Q i.1.core : ℝ))))) *
          ((A.responseParams.C₀ + 1) * (3 * G.spinActivity c i))
        = 9 * (A.responseParams.C₀ + 1) * e * tiltNearFactor R * G.spinActivity c i *
            Real.exp (-(2 * columnRate R * (setGap Q i.1.core : ℝ))) := by ring
      _ ≤ 9 * (A.responseParams.C₀ + 1) * e * tiltNearFactor R * G.spinActivity c i *
            (Real.exp (-(2 * rD)) * Real.exp (2 * columnRate R * (siteDiameter i.1.core : ℝ))) := by
          gcongr
      _ = (9 * (A.responseParams.C₀ + 1) * e * tiltNearFactor R * Real.exp (-(2 * rD))) *
            (G.spinActivity c i * 1 * Real.exp (2 * columnRate R * (siteDiameter i.1.core : ℝ))) := by
          ring
      _ ≤ _ := by gcongr
  have hKsum : ∑ i ∈ S, clusterCost A G c i ≤
      (20 * (A.responseParams.C₀ + 1) * clusterNearFactor R) * E8 * blockSumConstant :=
    sum_le_of_mem_core hgas hfit hc0 hcf hy₁ hrt hz0 Y S hSY (by positivity) fun i _ => le_refl _
  have hfinal : ∀ M : ℝ, 0 ≤ M →
      |∫ σ, ∑ i ∈ S, truncatedSpinPart A G h y M i σ ∂(tiltedGibbsLaw G Yt) -
          ∫ σ, ∑ i ∈ S, truncatedSpinPart A G h y M i σ ∂(G.gibbsLaw ∅)| ≤
        ((9 + 80 * Ci) * (A.responseParams.C₀ + 1) * blockSumConstant) * e * (Q.card : ℝ) *
          Real.exp (-(6 * c * R.coupling) - R.params.rt * D / 2 ^ 6) := by
    intro M hM
    have hin : ∀ (L : Measure G.Config) [IsProbabilityMeasure L] (i : G.GasSpin),
        Integrable (truncatedSpinPart A G h y M i) L :=
      fun L _ i => Integrable.of_bound (measurable_truncatedSpinPart st hset h y M i).aestronglyMeasurable M
        (Filter.Eventually.of_forall fun σ => by
          rw [Real.norm_eq_abs]
          exact abs_truncatedSpinPart_le hM i σ)
    rw [integral_finsetSum _ fun i _ => hin _ i, integral_finsetSum _ fun i _ => hin _ i, ← Finset.sum_sub_distrib]
    have hcard : (1 : ℝ) ≤ (Q.card : ℝ) := by exact_mod_cast hQ.card_pos
    have e1 : Real.exp (-(8 * (c * R.coupling))) = E8 := by
      rw [hE8]
      congr 1
      ring
    have hcn := final_bound_arith (C1 := A.responseParams.C₀ + 1) (e := e) (q := (Q.card : ℝ)) (Bb := tiltNearFactor R)
      (Bn := clusterNearFactor R) (W := blockSumConstant) (Ci := Ci)
      (cx := c * R.coupling) (rD := rD) hC1 he hcard hBb1 hBn1 blockSumConstant_nonneg hCi (by positivity) hrD0 hfloor
    rw [e1] at hcn
    have e2 : Real.exp (-(7 * (c * R.coupling)) - rD) = Real.exp (-(7 * c * R.coupling) - R.params.rt / 2 ^ 6 * D) := by
      congr 1
      rw [hrD]
      unfold columnRate
      ring
    have e3 : Real.exp (-(6 * (c * R.coupling)) - rD) = Real.exp (-(6 * c * R.coupling) - R.params.rt * D / 2 ^ 6) := by
      congr 1
      rw [hrD]
      unfold columnRate
      ring
    rw [e2, e3] at hcn
    calc _ ≤ ∑ i ∈ S, (Ai i + clusterCost A G c i * (2 * (2 * Ii))) :=
          (Finset.abs_sum_le_sum_abs _ _).trans (Finset.sum_le_sum fun i hi => hone i hi M hM)
      _ = ∑ i ∈ S, Ai i + (∑ i ∈ S, clusterCost A G c i) * (2 * (2 * Ii)) := by
          rw [Finset.sum_add_distrib, Finset.sum_mul]
      _ ≤ (9 * (A.responseParams.C₀ + 1) * e * tiltNearFactor R * Real.exp (-(2 * rD))) * E8 * blockSumConstant +
            ((20 * (A.responseParams.C₀ + 1) * clusterNearFactor R) * E8 * blockSumConstant) * (2 * (2 * Ii)) :=
          add_le_add hAsum (mul_le_mul_of_nonneg_right hKsum (by positivity))
      _ ≤ _ := by
          refine hcn.trans (le_of_eq ?_)
          ring
  exact classResponsePart_limit st hset hsz (tiltedGibbsLaw G Yt) (G.gibbsLaw ∅) hIν hIμ fun N =>
    hfinal N (Nat.cast_nonneg N)
end Close
end Closing
section Assembly
section Main
variable {R : StepSetup} {n : ℕ} [NeZero n]
theorem one_le_supportUnitCount {r : ℕ} {θ : GasSupport R n} (h : IsClusterSupport R.params.side r θ) :
    1 ≤ supportUnitCount R.params.side r θ := by apply _root_.YangMills.Construction.ClusterExpansionOfAStep.GasColumns.one_le_supportUnitCount <;> assumption
theorem floor_bound_arith {rt r L c x ng : ℝ} (hrt : 0 < rt) (hr : 1 ≤ r) (hL : 1 ≤ L) (hng : ng ≤ 10 * r + 1)
    (hcf : (2 ^ 16 + 2 ^ 7 * rt) * r ^ 4 ≤ c * x) :
    2 * (rt / 2 ^ 6) * (r / (4 * L) + 3) + rt / 2 ^ 6 * (ng + r / (4 * L) + 3 + 4) ≤ c * x := by
  have h1 : r / (4 * L) ≤ r := by
    rw [div_le_iff₀ (by positivity)]
    nlinarith
  have h2 : r ≤ r ^ 4 := by
    calc r = r ^ 1 := (pow_one r).symm
      _ ≤ r ^ 4 := pow_le_pow_right₀ hr (by norm_num)
  have h3 : rt * r ≤ 2 ^ 7 * rt * r ^ 4 := by nlinarith
  have h5 : 2 * (r / (4 * L) + 3) + (ng + r / (4 * L) + 3 + 4) ≤ 2 ^ 6 * r := by linarith
  have e : 2 * (rt / 2 ^ 6) * (r / (4 * L) + 3) + rt / 2 ^ 6 * (ng + r / (4 * L) + 3 + 4) =
      rt / 2 ^ 6 * (2 * (r / (4 * L) + 3) + (ng + r / (4 * L) + 3 + 4)) := by ring
  rw [e]
  calc _ ≤ rt / 2 ^ 6 * (2 ^ 6 * r) := mul_le_mul_of_nonneg_left h5 (by positivity)
    _ = rt * r := by ring
    _ ≤ _ := by linarith
set_option maxHeartbeats 4000000 in
theorem classResponsePartFarTilt_holds (hcols : ClusterExpansionOfAStep.GasColumnsSmall)
    (hpaid : ResponseInTheExpansion.clusterScoreIntegralBound)
    (htwo : WeightedResponses.ChartResponseComparison) (hT : LinearResponse.TiltedGibbsComparison)
    (hgas : StepGas.GasSumNearBlockBound) (hcf : TorusLumps.CouplingFloorExists)
    (hcfg : ClusterExpansionOfAStep.GasConfigIsAdmissibleSetting) (hmass : StepGas.SettingMassEqIntegral)
    (hpot : StepSettings.PotentialFactorization) (hagree : StepSettings.LocalSettingsAgree)
    (hborel : FreeEnergies.settingMeanMeasurableStatement) (hP : Dobrushin.MeanOfProductStatement)
    (hC : Dobrushin.ActivityConditionalLawsStatement) (hinf : ResponseInTheExpansion.farTiltInfluenceStatement) :
    ResponseInTheExpansion.classResponsePartFarTiltStatement := by
  classical
  obtain ⟨r₁, p₁, H₁⟩ := hcols
  obtain ⟨r₂, p₂, H₂⟩ := hpaid
  obtain ⟨r₃, p₃, H₃⟩ := htwo
  obtain ⟨r₄, p₄, H₄⟩ := hmass
  obtain ⟨r₅, p₅, H₅⟩ := hborel
  obtain ⟨r₈, p₈, H₈⟩ := hinf
  refine ⟨fun c => min (r₁ c) (min (r₂ c) (min (r₃ c) (min (r₄ c) (min (r₅ c) (r₈ c))))),
    fun c => lt_min (p₁ c) (lt_min (p₂ c) (lt_min (p₃ c) (lt_min (p₄ c) (lt_min (p₅ c) (p₈ c))))), fun T hT' hrt K => ?_⟩
  simp only [le_min_iff] at hrt
  obtain ⟨t₁, t₂, t₃, t₄, t₅, t₈⟩ := hrt
  obtain ⟨y₁, H₁⟩ := H₁ T hT' t₁
  obtain ⟨y₂, H₂⟩ := H₂ T hT' t₂ K
  obtain ⟨y₃, H₃⟩ := H₃ T hT' t₃ K
  obtain ⟨y₄, H₄⟩ := H₄ T hT' t₄
  obtain ⟨y₅, H₅⟩ := H₅ T hT' t₅ K
  obtain ⟨y₆, H₆⟩ := hcfg T hT'
  obtain ⟨y₈, Ci, hCi, H₈⟩ := H₈ T hT' t₈ K
  have hrt0 := hT'.rt_pos
  have hch : 0 < T.gasRate := by
    have h1 := hT'.cE_pos
    have h2 := hT'.κ_pos
    have h3 := hT'.σ_pos
    unfold ParameterAssignment.gasRate ParameterAssignment.κ₁
    positivity
  obtain ⟨y₇, H₇⟩ := hcf T.gasRate T.side T.rt hch
  obtain ⟨y₉, H₉⟩ := hcf T.gasRate (8 * T.side) T.rt hch
  refine ⟨max T.floorMin (max y₁ (max y₂ (max y₃ (max y₄ (max y₅ (max y₆ (max y₇ (max y₈ (max y₉ (200 * T.B)))))))))),
    (9 + 80 * Ci) * (|K.C₀| + 1) * blockSumConstant, ?_,
    fun y hy R A hK hAT n _ G hG h yy Q B e Yt D hsz hDr hQ hD hB he ht => ?_⟩
  · have := blockSumConstant_nonneg
    positivity
  simp only [max_le_iff] at hy
  obtain ⟨hy0, hy1, hy2, hy3, hy4, hy5, hy6, hy7, hy8, hy9, hyB⟩ := hy
  have hOT := hAT.onFamily
  obtain ⟨hR, hρA, hpc, hyx, hstep⟩ := id hOT
  have hx1 : 1 ≤ R.coupling := by
    have h1 : (1 : ℝ) ≤ T.floorMin := by
      have h2 := hT'.yC_ge
      exact h2.trans (le_max_left _ _)
    linarith only [h1, hy0, hyx]
  have hx0 : 0 < R.coupling := by linarith only [hx1]
  have hL : R.params.side = T.side := by rw [hR]; rfl
  have hRrt : R.params.rt = T.rt := by rw [hR]; rfl
  have hRa : R.params.coupling = T.coupling := by rw [hR]; rfl
  have hRσ : R.params.threshold = T.threshold := by rw [hR]; rfl
  have hRy : R.params.y₁ = y := by rw [hR]; rfl
  have hfit : R.params.Admissible := by rw [hR]; exact hT'.fits y hy0
  have hodd : Odd R.params.side := by rw [hL]; exact hT'.L_odd
  have hx' : R.nextCoupling ≤ 1.01 * R.coupling := by
    have h1 := (abs_le.mp hAT.abs_sub_le).2
    linarith only [h1, hyB, hyx]
  have hrtR : 0 < R.params.rt := by rw [hRrt]; exact hrt0
  have hn : R.params.n₀ ≤ n := by
    rcases hG with h | h
    · exact h.n₀_le
    · have h1 := h.isBlockSide.2
      have hL1 : 1 ≤ R.params.side := Nat.pos_of_ne_zero (NeZero.ne _)
      nlinarith only [h1, hL1]
  have hRn₀ : R.params.n₀ = T.n₀ := by rw [hR]; rfl
  have hside : IsBlockTorusSide R.params (n * R.params.side) :=
    ⟨Dvd.intro_left n rfl, by rw [mul_comm R.params.side]; exact Nat.mul_le_mul_right _ hn⟩
  have hadm : ∀ σ, G.pairConstraint.IsAdmissible σ → (configSetting G σ).IsAdmissible := fun σ hσ =>
    H₆ y hy6 R hOT hx' n G hG σ hσ
  have hρR : 0 < R.ballRadius := by
    show 0 < R.params.threshold / 64
    rw [hRσ]
    have := hT'.σ_pos
    positivity
  have hρπ : R.anchorRadius + R.ballRadius < Real.pi := by
    have h1 := hT'.chain.2.2.2.2.1
    have h3 := hT'.σ_one
    have h4 := Real.pi_gt_three
    have e : R.ballRadius = T.threshold / 64 := by
      show R.params.threshold / 64 = _
      rw [hRσ]
    rw [hρA, e]
    linarith only [h1, h3, h4]
  have hρA0 : 0 < R.anchorRadius := by
    rw [hρA]
    exact hT'.chain.2.2.2.1
  have hall : G.pairConstraint.IsAdmissible (fun i => G.pairConstraint.vacant i) := fun a b _ =>
    G.pairConstraint.vacant_compatible _ _ _
  have hzero : (configSetting G fun i => G.pairConstraint.vacant i).InBalls 0 := fun b => by
    rw [ClusterExpansionOfAStep.coordNorm_eq_norm]
    simpa using hρR.le
  have hflat := (hpot R hfit hstep.1 hρA0 hρπ n hn _ (hadm _ hall) 0 hzero).1
  have ha1 : 1 ≤ R.params.coupling := by rw [hRa]; exact hT'.a_ge
  have hl := hAT.admissible.params_admissible
  have hc0' : 12 + 40 * R.params.coupling ≤ A.responseParams.C₀ := by
    have h1 := hl.C₀_eq
    have h2 := hl.N₀_nonneg
    have h3 := hl.Kc_ge
    linarith only [h1, h2, h3]
  have st : FarTiltContext A G := {
    response := hAT.admissible
    params_admissible := hfit
    side_odd := hodd
    hullExpansion := hstep.1.2
    blockSide := hside
    n₀_le := hn
    functional_trivial_pos := hflat
    setting_admissible := hadm
    chartDensity_facts := fun σ hσ => by
      obtain ⟨a1, a2, -⟩ := H₄ y hy4 R hOT n (by rw [← hRn₀]; exact hn) (configSetting G σ) (hadm σ hσ)
      exact ⟨a1, a2⟩
    settingsAgree := hagree
    settingMean_measurable := fun F hF => H₅ y hy5 R A hK hAT n G hG F hF
    one_le_coupling := ha1
    C₀_ge := hc0'
    chartResponse_near := fun s s' Y m hs hs' hag hm o ho h =>
      (((H₃ y hy3 R A hK hAT).2 n n s s' Y Y m hn hn hs hs').1 hag hm).1 o ho h h fun _ _ _ _ _ => rfl }
  obtain ⟨hw, cols⟩ := H₁ y hy1 R hOT hx' n G hG fun j => j.1.Touches ∅
  have paid := H₂ y hy2 R A hK hAT n G hG
  have hcfR : R.params.RangeFloor T.gasRate := by
    intro x hx
    have := H₇ x (hy7.trans (hRy ▸ hx))
    rw [hL, hRrt]
    exact this
  have hyR : R.params.y₁ ≤ R.coupling := by rw [hRy]; exact hyx
  have hhalf := cols.exp_le_half
  have hz2 : ∀ i, G.spinActivity T.gasRate i ≤ 1 / 2 := fun i => by
    refine le_trans ?_ hhalf
    show Real.exp _ ≤ _
    apply Real.exp_le_exp.mpr
    have hu : (1 : ℝ) ≤ (supportUnitCount R.params.side R.range i.1 : ℝ) := by
      exact_mod_cast one_le_supportUnitCount i.2.isCluster
    have hcx : 0 ≤ T.gasRate * R.coupling := by positivity
    nlinarith
  have hr8 : 8 * R.params.side ≤ R.range := by
    have := (H₉ R.coupling (hy9.trans hyx)).1
    rw [hL]
    exact this
  have hfloor : tiltNearFactor R * clusterNearFactor R * Real.exp (-(T.gasRate * R.coupling)) ≤ 1 := by
    obtain ⟨c1, c2⟩ := hcfR R.coupling hyR
    have hr1 : (1 : ℝ) ≤ (clusterRange R.coupling : ℝ) := by
      have : 1 ≤ clusterRange R.coupling := Nat.ceil_pos.mpr (Real.rpow_pos_of_pos hx0 _)
      exact_mod_cast this
    have hL1 : (1 : ℝ) ≤ (R.params.side : ℝ) := by
      have : 1 ≤ R.params.side := Nat.pos_of_ne_zero (NeZero.ne _)
      exact_mod_cast this
    have hng : (nearGap R.params.side (clusterRange R.coupling) : ℝ) ≤ 10 * (clusterRange R.coupling : ℝ) + 1 := by
      have : nearGap R.params.side (clusterRange R.coupling) ≤ 10 * clusterRange R.coupling + 1 := by
        unfold nearGap
        have := Nat.div_le_self (10 * clusterRange R.coupling) R.params.side
        omega
      exact_mod_cast this
    have key := floor_bound_arith hrtR hr1 hL1 hng c2
    unfold tiltNearFactor clusterNearFactor columnRate nearRadius
    rw [← Real.exp_add, ← Real.exp_add]
    apply Real.exp_le_one_iff.mpr
    have e1 : (R.range : ℝ) = (clusterRange R.coupling : ℝ) := rfl
    rw [e1]
    have e2 : (nearGap R.params.side R.range : ℝ) = (nearGap R.params.side (clusterRange R.coupling) : ℝ) := rfl
    rw [e2]
    linarith only [key]
  have hinf' := H₈ y hy8 R A hK hAT n G hG {parentBlock R.params.side yy} Q e D (Finset.singleton_nonempty _) hQ he hDr
    (fun Y hY Y' hY' => by
      rw [Finset.mem_singleton.mp hY]
      exact hD Y' hY')
  have res := classResponsePart_bound hT hP hgas hC st hch hcfR hyR hrtR he hr8 hx0.le hw cols paid ht hz2 hfloor hCi hsz
    hB hQ hD hinf'
  rw [hK] at res
  refine ⟨res.1, res.2.1, res.2.2.trans ?_⟩
  have hW := blockSumConstant_nonneg
  have hq : (0 : ℝ) ≤ (Q.card : ℝ) := Nat.cast_nonneg _
  have he0 : (0 : ℝ) ≤ e := by linarith only [he]
  have hK1 : K.C₀ + 1 ≤ |K.C₀| + 1 := by linarith only [le_abs_self K.C₀]
  have hmid : (9 + 80 * Ci) * (K.C₀ + 1) * blockSumConstant ≤ (9 + 80 * Ci) * (|K.C₀| + 1) * blockSumConstant :=
    mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left hK1 (by positivity)) hW
  exact mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right hmid he0) hq)
    (Real.exp_pos _).le
end Main
end Assembly
end FarTiltClassPart
theorem classResponsePartFarTilt (hcols : ClusterExpansionOfAStep.GasColumnsSmall)
    (hpaid : ResponseInTheExpansion.clusterScoreIntegralBound)
    (htwo : WeightedResponses.ChartResponseComparison) (hT : LinearResponse.TiltedGibbsComparison)
    (hgas : StepGas.GasSumNearBlockBound) (hcf : TorusLumps.CouplingFloorExists)
    (hcfg : ClusterExpansionOfAStep.GasConfigIsAdmissibleSetting) (hmass : StepGas.SettingMassEqIntegral)
    (hpot : StepSettings.PotentialFactorization) (hagree : StepSettings.LocalSettingsAgree)
    (hborel : FreeEnergies.settingMeanMeasurableStatement) (hP : Dobrushin.MeanOfProductStatement)
    (hC : Dobrushin.ActivityConditionalLawsStatement) (hinf : ResponseInTheExpansion.farTiltInfluenceStatement) :
    ResponseInTheExpansion.classResponsePartFarTiltStatement := by apply _root_.YangMills.Construction.ResponseInTheExpansion.FarTiltClassPart.classResponsePartFarTilt_holds <;> assumption
end ResponseInTheExpansion
end YangMills.Construction
end
