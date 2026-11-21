import YangMills.Construction.InfiniteLattice.ContinuousLocalObservablesDecideAndWeakCompactness
import YangMills.Construction.InfiniteLattice.RulesOfTheActionOfTheLatticeIsometries
import YangMills.Construction.InfiniteLattice.SpaceOfConfigurationsAndSpaceOfMeasures
import YangMills.Construction.InfiniteLattice.StatesWithAGivenMirrorDominateLocalObservablesProof
import YangMills.Construction.InfiniteLattice.WhatAnObservableDependsOnAndItsSupport
import Mathlib
set_option autoImplicit false
open Filter MeasureTheory Set TopologicalSpace
open scoped Topology
noncomputable section
namespace YangMills.Construction.InfiniteLattice.LocalDetermination
theorem integrable_of_isBoundedObservable {F : GaugeField 1 → ℂ} (hF : IsBoundedObservable F)
    (m : Measure (GaugeField 1)) [IsFiniteMeasure m] : Integrable F m := by apply _root_.YangMills.Construction.InfiniteLattice.MirrorDomination.integrable_of_isBoundedObservable <;> assumption
section Compact
variable [CompactSpace (GaugeField 1)] [MetrizableSpace (GaugeField 1)]
omit [MetrizableSpace (GaugeField 1)] in
theorem isBoundedObservable_of_continuous {F : GaugeField 1 → ℂ} (hF : Continuous F) :
    IsBoundedObservable F := by apply _root_.YangMills.Construction.InfiniteLattice.MirrorDomination.isBoundedObservable_of_continuous <;> assumption
omit [MetrizableSpace (GaugeField 1)] in
theorem supNorm_coe (f : C(GaugeField 1, ℂ)) :
    observableSupNorm (f : GaugeField 1 → ℂ) = ‖f‖ := by
  rw [ContinuousMap.norm_eq_iSup_norm]
  rfl
omit [MetrizableSpace (GaugeField 1)] in
theorem mem_continuousLocalFunctions
    (hdep : ObservableDependence.Statement) {F : GaugeField 1 → ℂ}
    (hF : F ∈ FieldsAtSpacing.continuousFiniteLinkFunctions 1) :
    F ∈ continuousLocalFunctions 1 := by
  obtain ⟨hc, S, hfin, hsub, f, -, hf⟩ := hF
  have hc : Continuous F := hc
  have hb := isBoundedObservable_of_continuous hc
  refine ⟨hb, ?_, hc⟩
  have hset : IsLinkSet S := fun b hb => mem_positiveLinks_iff.1 (hsub hb)
  have hon : DependsOnlyOn S F := by
    intro U V h
    rw [hf U, hf V]
    congr 1
    funext b
    exact h b b.2
  exact (hdep F hb S S hset hset univ).2.2.2.1.2 ⟨S, hset, hfin, hon⟩
omit [MetrizableSpace (GaugeField 1)] in
theorem exists_local_approx
    (hdense : FieldsAtSpacing.ContinuousFiniteLinkFunctionsDense 1)
    (hdep : ObservableDependence.Statement) (f : C(GaugeField 1, ℂ)) {ε : ℝ}
    (hε : 0 < ε) :
    ∃ g : C(GaugeField 1, ℂ), (g : GaugeField 1 → ℂ) ∈ continuousLocalFunctions 1 ∧
      ‖f - g‖ < ε := by
  obtain ⟨G, hG, h⟩ := hdense.2.2.2.2 f f.continuous ε hε
  have hl := mem_continuousLocalFunctions hdep hG
  refine ⟨⟨G, hl.2.2⟩, hl, ?_⟩
  rw [← supNorm_coe]
  exact h
theorem exists_countable_dense
    (hdense : FieldsAtSpacing.ContinuousFiniteLinkFunctionsDense 1)
    (hdep : ObservableDependence.Statement) :
    ∃ D : Set (GaugeField 1 → ℂ), D.Countable ∧ D ⊆ continuousLocalFunctions 1 ∧
      ∀ F : GaugeField 1 → ℂ, Continuous F →
        ∀ ε : ℝ, 0 < ε → ∃ H ∈ D, observableSupNorm (F - H) < ε := by
  have : SecondCountableTopology (GaugeField 1) := by
    let := metrizableSpaceMetric (GaugeField 1)
    infer_instance
  let T : Set C(GaugeField 1, ℂ) :=
    {g | (g : GaugeField 1 → ℂ) ∈ continuousLocalFunctions 1}
  obtain ⟨t, htT, htc, hcl⟩ := (IsSeparable.of_separableSpace T).exists_countable_dense_subset
  refine ⟨(fun g : C(GaugeField 1, ℂ) => (g : GaugeField 1 → ℂ)) '' t, htc.image _, ?_, ?_⟩
  · rintro _ ⟨g, hg, rfl⟩
    exact htT hg
  · intro F hF ε hε
    obtain ⟨g, hg, hfg⟩ := exists_local_approx hdense hdep ⟨F, hF⟩ (half_pos hε)
    obtain ⟨H, hH, hgH⟩ := Metric.mem_closure_iff.1 (hcl hg) (ε / 2) (half_pos hε)
    refine ⟨H, ⟨H, hH, rfl⟩, ?_⟩
    have hn : observableSupNorm (F - (H : GaugeField 1 → ℂ)) =
        ‖(⟨F, hF⟩ : C(GaugeField 1, ℂ)) - H‖ :=
      supNorm_coe ((⟨F, hF⟩ : C(GaugeField 1, ℂ)) - H)
    rw [hn]
    have h1 : ‖g - H‖ < ε / 2 := by rwa [← dist_eq_norm]
    calc ‖(⟨F, hF⟩ : C(GaugeField 1, ℂ)) - H‖
        ≤ ‖(⟨F, hF⟩ : C(GaugeField 1, ℂ)) - g‖ + ‖g - H‖ :=
          norm_sub_le_norm_sub_add_norm_sub _ _ _
      _ < ε := by linarith
theorem stateEval_eq_of_continuous
    (hdense : FieldsAtSpacing.ContinuousFiniteLinkFunctionsDense 1)
    (hdep : ObservableDependence.Statement)
    (ν ν' : Measure (GaugeField 1)) [IsProbabilityMeasure ν] [IsProbabilityMeasure ν']
    (h : ∀ F ∈ continuousLocalFunctions 1, stateEval ν F = stateEval ν' F)
    {F : GaugeField 1 → ℂ} (hF : Continuous F) : stateEval ν F = stateEval ν' F := by
  have key : ∀ ε : ℝ, 0 < ε → ‖stateEval ν F - stateEval ν' F‖ ≤ 0 + ε := by
    intro ε hε
    obtain ⟨g, hg, hfg⟩ := exists_local_approx hdense hdep ⟨F, hF⟩ (half_pos hε)
    have bound : ∀ (m : Measure (GaugeField 1)) [IsProbabilityMeasure m],
        ‖stateEval m F - stateEval m (g : GaugeField 1 → ℂ)‖ ≤ ε / 2 := by
      intro m _
      have iF := integrable_of_isBoundedObservable (isBoundedObservable_of_continuous hF) m
      have ig := integrable_of_isBoundedObservable (isBoundedObservable_of_continuous g.continuous) m
      have e : stateEval m F - stateEval m (g : GaugeField 1 → ℂ) =
          ∫ U, (F U - g U) ∂m := (integral_sub iF ig).symm
      rw [e]
      have hb : ∀ᵐ U ∂m, ‖F U - g U‖ ≤ ε / 2 := Eventually.of_forall fun U =>
        (ContinuousMap.norm_coe_le_norm ((⟨F, hF⟩ : C(GaugeField 1, ℂ)) - g) U).trans hfg.le
      simpa using norm_integral_le_of_norm_le_const hb
    have e := h _ hg
    have b1 := bound ν
    have b2 := bound ν'
    rw [e] at b1
    have : stateEval ν F - stateEval ν' F =
        (stateEval ν F - stateEval ν' (g : GaugeField 1 → ℂ)) -
          (stateEval ν' F - stateEval ν' (g : GaugeField 1 → ℂ)) := by ring
    rw [this]
    calc _ ≤ _ := norm_sub_le _ _
      _ ≤ 0 + ε := by linarith
  exact sub_eq_zero.1 (norm_le_zero_iff.1 (le_of_forall_pos_le_add key))
theorem eq_of_stateEval_eq
    (hdense : FieldsAtSpacing.ContinuousFiniteLinkFunctionsDense 1)
    (hdep : ObservableDependence.Statement)
    (ν ν' : Measure (GaugeField 1)) [IsProbabilityMeasure ν] [IsProbabilityMeasure ν']
    (h : ∀ F ∈ continuousLocalFunctions 1, stateEval ν F = stateEval ν' F) : ν = ν' := by
  let := metrizableSpaceMetric (GaugeField 1)
  refine ext_of_forall_integral_eq_of_IsFiniteMeasure fun f => ?_
  have hc : Continuous fun U => ((f U : ℝ) : ℂ) := Complex.continuous_ofReal.comp f.continuous
  have e := stateEval_eq_of_continuous hdense hdep ν ν' h hc
  have e' : ∫ U, ((f U : ℝ) : ℂ) ∂ν = ∫ U, ((f U : ℝ) : ℂ) ∂ν' := e
  rw [integral_complex_ofReal, integral_complex_ofReal] at e'
  exact_mod_cast e'
theorem exists_weak_subseq (μ : ℕ → Measure (GaugeField 1))
    (hμ : ∀ k, 1 ≤ k → IsProbabilityMeasure (μ k)) :
    ∃ (κ : ℕ → ℕ) (ν : Measure (GaugeField 1)), IsProbabilityMeasure ν ∧
      (∀ j, 1 ≤ j → 1 ≤ κ j) ∧ (∀ i j, 1 ≤ i → i < j → κ i < κ j) ∧
      WeakConvergesUnitSpacing (fun j => μ (κ j)) ν := by
  have : SeparableSpace (GaugeField 1) := by
    let := metrizableSpaceMetric (GaugeField 1)
    infer_instance
  let P : ℕ → ProbabilityMeasure (GaugeField 1) :=
    fun k => ⟨μ (k + 1), hμ _ (Nat.le_add_left 1 k)⟩
  obtain ⟨Q, φ, hφ, hQ⟩ := CompactSpace.tendsto_subseq P
  refine ⟨fun j => φ j + 1, (Q : Measure (GaugeField 1)), inferInstance,
    fun j _ => Nat.le_add_left 1 _, fun i j _ hij => Nat.add_lt_add_right (hφ hij) 1,
    fun F hF => ?_⟩
  exact (ProbabilityMeasure.tendsto_iff_forall_integral_rclike_tendsto ℂ).1 hQ
    (BoundedContinuousFunction.mkOfCompact ⟨F, hF⟩)
theorem isSymmetricUnder_of_stateEval_eq
    (hdense : FieldsAtSpacing.ContinuousFiniteLinkFunctionsDense 1)
    (hdep : ObservableDependence.Statement) (r : LatticeSymmetry 1)
    (hr : ∃ e : GaugeField 1 ≃ₜ GaugeField 1, ⇑e = r.pullbackField)
    (ν : Measure (GaugeField 1)) [IsProbabilityMeasure ν]
    (h : ∀ F ∈ continuousLocalFunctions 1, stateEval ν (r.actOn F) = stateEval ν F) :
    IsSymmetricUnder ν r := by
  obtain ⟨e, he⟩ := hr
  have hmap : ∀ F : GaugeField 1 → ℂ,
      ∫ U, F U ∂(ν.map e) = ∫ U, r.actOn F U ∂ν := fun F => by
    rw [e.measurableEmbedding.integral_map, he]
    rfl
  have : IsProbabilityMeasure (ν.map e) :=
    Measure.isProbabilityMeasure_map e.measurable.aemeasurable
  have heq : ν.map e = ν :=
    eq_of_stateEval_eq hdense hdep _ _ fun F hF => (hmap F).trans (h F hF)
  intro A _
  rw [← hmap A, heq]
theorem isSymmetricUnder_of_weak_limit
    (hdense : FieldsAtSpacing.ContinuousFiniteLinkFunctionsDense 1)
    (hdep : ObservableDependence.Statement) (r : LatticeSymmetry 1)
    (hr : ∃ e : GaugeField 1 ≃ₜ GaugeField 1, ⇑e = r.pullbackField)
    (μ : ℕ → Measure (GaugeField 1)) (ν : Measure (GaugeField 1))
    (hν : IsProbabilityMeasure ν) (hlim : WeakConvergesUnitSpacing μ ν)
    (hinv : ∀ k, 1 ≤ k → IsSymmetricUnder (μ k) r) : IsSymmetricUnder ν r := by
  refine isSymmetricUnder_of_stateEval_eq hdense hdep r hr ν fun F hF => ?_
  obtain ⟨e, he⟩ := hr
  have hrF : Continuous (r.actOn F) := by
    have : r.actOn F = F ∘ e := by
      rw [he]
      rfl
    rw [this]
    exact hF.2.2.comp e.continuous
  refine tendsto_nhds_unique_of_eventuallyEq (hlim _ hrF) (hlim F hF.2.2) ?_
  filter_upwards [eventually_ge_atTop 1] with k hk
  exact hinv k hk F hF.1
end Compact
theorem localDeterminationAndCompactness_holds (hrules : SymmetryActionRules.Statement)
    (hdep : ObservableDependence.Statement)
    (hspace : FieldsAtSpacing.CompactFieldsAndMeasures) :
    LocalDeterminationAndCompactness := by
  obtain ⟨⟨-, -, -, -, hc, hm, -, -⟩, hdense, -, -⟩ := hspace 1 one_pos
  have := hc
  have := hm
  have hr : ∀ r : LatticeSymmetry 1,
      ∃ e : GaugeField 1 ≃ₜ GaugeField 1, ⇑e = r.pullbackField := fun r =>
    (hrules r r).2.2.2.2.2.2.2.2.2.2.1
  refine ⟨exists_countable_dense hdense hdep, fun ν ν' _ _ h => eq_of_stateEval_eq hdense hdep ν ν' h,
    exists_weak_subseq, fun r => ⟨fun ν _ h =>
      isSymmetricUnder_of_stateEval_eq hdense hdep r (hr r) ν h, fun μ ν _ hν hlim hinv =>
      isSymmetricUnder_of_weak_limit hdense hdep r (hr r) μ ν hν hlim hinv⟩⟩
end YangMills.Construction.InfiniteLattice.LocalDetermination
