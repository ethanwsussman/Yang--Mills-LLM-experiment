import YangMills.Construction.ClusterExpansionOfAStep.OrderOfTheBlocks
import Mathlib
set_option autoImplicit false
noncomputable section
open MeasureTheory
namespace YangMills.Construction.BlockOrder
theorem pi_map_comp_injective {I K : Type} [Fintype I] [Fintype K] (e : K → I) (he : Function.Injective e)
    (ν : Measure ℝ) [IsProbabilityMeasure ν] :
    Measure.map (fun u : I → ℝ => u ∘ e) (Measure.pi fun _ : I => ν) = Measure.pi fun _ : K => ν := by
  classical
  have hm : Measurable fun u : I → ℝ => u ∘ e := measurable_pi_iff.mpr fun k => measurable_pi_apply (e k)
  symm
  refine Measure.pi_eq fun B hB => ?_
  rw [Measure.map_apply hm (MeasurableSet.univ_pi hB)]
  let C : I → Set ℝ := fun i => if h : ∃ k, e k = i then B h.choose else Set.univ
  have hC : ∀ k, C (e k) = B k := by
    intro k
    have h : ∃ k', e k' = e k := ⟨k, rfl⟩
    simp only [C, dif_pos h]
    rw [he h.choose_spec]
  have hpre : (fun u : I → ℝ => u ∘ e) ⁻¹' Set.univ.pi B = Set.univ.pi C := by
    ext u
    simp only [Set.mem_preimage, Set.mem_pi, Set.mem_univ, true_implies, Function.comp]
    constructor
    · intro h i
      by_cases hi : ∃ k, e k = i
      · obtain ⟨k, rfl⟩ := hi
        rw [hC]
        exact h k
      · simp [C, dif_neg hi]
    · intro h k
      have := h (e k)
      rwa [hC] at this
  rw [hpre, Measure.pi_pi]
  symm
  refine Fintype.prod_of_injective e he _ _ ?_ ?_
  · intro i hi
    have hi' : ¬ ∃ k, e k = i := fun ⟨k, hk⟩ => hi ⟨k, hk⟩
    simp [C, dif_neg hi']
  · intro k
    rw [hC]
instance uniformUnitInterval_isProbability : IsProbabilityMeasure (volume.restrict (Set.Icc (0 : ℝ) 1)) :=
  ⟨by simp⟩
theorem pi_uniform_coincidence_null {I : Type} [Fintype I] {i j : I} (hij : i ≠ j) :
    Measure.pi (fun _ : I => volume.restrict (Set.Icc (0 : ℝ) 1)) {u : I → ℝ | u i = u j} = 0 := by
  classical
  set ν : Measure ℝ := volume.restrict (Set.Icc (0 : ℝ) 1) with hν
  let e : Fin 2 → I := ![i, j]
  have he : Function.Injective e := by
    intro a b hab
    fin_cases a <;> fin_cases b <;> simp_all [e, hij, hij.symm]
  have hset : MeasurableSet {w : Fin 2 → ℝ | w 0 = w 1} :=
    measurableSet_eq_fun (measurable_pi_apply 0) (measurable_pi_apply 1)
  have hm : Measurable fun u : I → ℝ => u ∘ e := measurable_pi_iff.mpr fun k => measurable_pi_apply (e k)
  have h1 : {u : I → ℝ | u i = u j} = (fun u : I → ℝ => u ∘ e) ⁻¹' {w : Fin 2 → ℝ | w 0 = w 1} := by
    ext u
    simp [e]
  rw [h1, ← Measure.map_apply hm hset, pi_map_comp_injective e he ν]
  have h2 := (measurePreserving_finTwoArrow ν).measure_preimage_equiv
    (s := {p : ℝ × ℝ | p.1 = p.2})
  have h3 : (MeasurableEquiv.finTwoArrow : (Fin 2 → ℝ) ≃ᵐ ℝ × ℝ) ⁻¹' {p : ℝ × ℝ | p.1 = p.2} =
      {w : Fin 2 → ℝ | w 0 = w 1} := by
    ext w
    simp [MeasurableEquiv.finTwoArrow]
  rw [← h3, h2]
  have hd : MeasurableSet {p : ℝ × ℝ | p.1 = p.2} := measurableSet_eq_fun measurable_fst measurable_snd
  rw [Measure.prod_apply hd]
  have : ∀ x : ℝ, ν (Prod.mk x ⁻¹' {p : ℝ × ℝ | p.1 = p.2}) = 0 := by
    intro x
    have : Prod.mk x ⁻¹' {p : ℝ × ℝ | p.1 = p.2} = {x} := by
      ext y
      simp [eq_comm]
    rw [this]
    exact measure_singleton x
  simp [this]
theorem randomOrderFacts_holds : YangMills.Construction.BlockOrder.RandomOrderFacts := by
  intro n _
  have hp : IsProbabilityMeasure (YangMills.Construction.MarkedIntegrals.randomOrderLaw n) := by
    unfold YangMills.Construction.MarkedIntegrals.randomOrderLaw
    infer_instance
  refine ⟨hp, ?_, ?_, ?_⟩
  · classical
    have hall : ∀ᵐ u ∂YangMills.Construction.MarkedIntegrals.randomOrderLaw n,
        ∀ i j : YangMills.Construction.TorusFields.TorusSite n, i ≠ j → u i ≠ u j := by
      rw [ae_all_iff]
      intro i
      rw [ae_all_iff]
      intro j
      by_cases hij : i = j
      · exact Filter.Eventually.of_forall fun u h => absurd hij h
      · have h0 : YangMills.Construction.MarkedIntegrals.randomOrderLaw n
            {u : YangMills.Construction.TorusFields.TorusSite n → ℝ | u i = u j} = 0 :=
          pi_uniform_coincidence_null hij
        have : ∀ᵐ u ∂YangMills.Construction.MarkedIntegrals.randomOrderLaw n,
            u ∉ {u : YangMills.Construction.TorusFields.TorusSite n → ℝ | u i = u j} :=
          measure_eq_zero_iff_ae_notMem.mp h0
        filter_upwards [this] with u hu _ h
        exact hu h
    filter_upwards [hall] with u hu i j hij
    by_contra h
    exact hu i j h hij
  · intro f Y
    classical
    letI : MeasurableSpace (Finset (YangMills.Construction.TorusFields.TorusSite n)) := ⊤
    have hmem : ∀ i : YangMills.Construction.TorusFields.TorusSite n,
        MeasurableSet {u : YangMills.Construction.TorusFields.TorusSite n → ℝ |
          i ∈ YangMills.Construction.MarkedIntegrals.precedingBlocks u Y} := by
      intro i
      have : {u : YangMills.Construction.TorusFields.TorusSite n → ℝ |
          i ∈ YangMills.Construction.MarkedIntegrals.precedingBlocks u Y} = {u | u i < u Y} := by
        ext u
        simp [YangMills.Construction.MarkedIntegrals.precedingBlocks]
      rw [this]
      exact measurableSet_lt (measurable_pi_apply i) (measurable_pi_apply Y)
    have hm : Measurable fun u : YangMills.Construction.TorusFields.TorusSite n → ℝ =>
        YangMills.Construction.MarkedIntegrals.precedingBlocks u Y := by
      refine measurable_to_countable' fun A => ?_
      have : (fun u : YangMills.Construction.TorusFields.TorusSite n → ℝ =>
          YangMills.Construction.MarkedIntegrals.precedingBlocks u Y) ⁻¹' {A} =
          ⋂ i, {u | i ∈ YangMills.Construction.MarkedIntegrals.precedingBlocks u Y ↔ i ∈ A} := by
        ext u
        simp only [Set.mem_preimage, Set.mem_singleton_iff, Set.mem_iInter, Set.mem_setOf_eq]
        exact Finset.ext_iff
      rw [this]
      refine MeasurableSet.iInter fun i => ?_
      by_cases hi : i ∈ A
      · have : {u : YangMills.Construction.TorusFields.TorusSite n → ℝ |
            i ∈ YangMills.Construction.MarkedIntegrals.precedingBlocks u Y ↔ i ∈ A} =
            {u | i ∈ YangMills.Construction.MarkedIntegrals.precedingBlocks u Y} := by
          ext u
          simp [hi]
        rw [this]
        exact hmem i
      · have : {u : YangMills.Construction.TorusFields.TorusSite n → ℝ |
            i ∈ YangMills.Construction.MarkedIntegrals.precedingBlocks u Y ↔ i ∈ A} =
            {u | i ∈ YangMills.Construction.MarkedIntegrals.precedingBlocks u Y}ᶜ := by
          ext u
          simp [hi]
        rw [this]
        exact (hmem i).compl
    have hf : Measurable fun u => f (YangMills.Construction.MarkedIntegrals.precedingBlocks u Y) :=
      (measurable_from_top (f := f)).comp hm
    refine Integrable.of_bound hf.aestronglyMeasurable
      (∑ A : Finset (YangMills.Construction.TorusFields.TorusSite n), |f A|)
      (Filter.Eventually.of_forall fun u => ?_)
    rw [Real.norm_eq_abs]
    exact Finset.single_le_sum (f := fun A => |f A|) (fun _ _ => abs_nonneg _) (Finset.mem_univ _)
  · intro K _ e he
    exact pi_map_comp_injective e he _
end YangMills.Construction.BlockOrder
end
