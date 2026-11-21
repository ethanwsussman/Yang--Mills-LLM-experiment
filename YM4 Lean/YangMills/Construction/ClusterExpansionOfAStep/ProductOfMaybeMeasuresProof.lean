import YangMills.Construction.ClusterExpansionOfAStep.ProductOfMaybeMeasures
import Mathlib
set_option autoImplicit false
noncomputable section
open MeasureTheory
namespace YangMills.Construction.TorusLumps
namespace WithNoneProduct
variable {I : Type} {S : I → Type}
theorem measurable_valuesOn [∀ i, MeasurableSpace (S i)] (Γ : Finset I) :
    Measurable (valuesOn (S := S) Γ) := by
  classical
  refine measurable_pi_lambda _ fun i => ?_
  unfold valuesOn
  by_cases h : i ∈ Γ
  · simp only [dif_pos h]
    exact measurable_inr.comp (measurable_pi_apply _)
  · simp only [dif_neg h]
    exact measurable_const
theorem withNoneMeasure_apply {α : Type} [MeasurableSpace α] (μ : Measure α) {s : Set (WithNone α)}
    (hs : MeasurableSet s) :
    withNoneMeasure μ s = (open Classical in if Sum.inl () ∈ s then 1 else 0) + μ (Sum.inr ⁻¹' s) := by
  classical
  unfold withNoneMeasure
  rw [Measure.add_apply, Measure.map_apply measurable_inl hs, Measure.map_apply measurable_inr hs]
  congr 1
  by_cases h : Sum.inl () ∈ s
  · rw [if_pos h, Measure.dirac_apply' _ (measurable_inl hs)]
    simp [h]
  · rw [if_neg h, Measure.dirac_apply' _ (measurable_inl hs)]
    simp [h]
end WithNoneProduct
open WithNoneProduct in
theorem lintegralPiWithNone_holds : LintegralPiWithNone := by
  classical
  intro I _ S _ ν _ _ f hf
  have hsum : Measure.pi (fun i => withNoneMeasure (ν i)) =
      ∑ Γ : Finset I, Measure.map (valuesOn Γ) (Measure.pi fun i : Γ => ν i) := by
    refine Measure.pi_eq fun s hs => ?_
    rw [Measure.finsetSum_apply]
    have hbox : ∀ Γ : Finset I, Measure.map (valuesOn Γ) (Measure.pi fun i : Γ => ν i) (Set.univ.pi s) =
        (∏ i ∈ Finset.univ \ Γ, (if Sum.inl () ∈ s i then (1 : ENNReal) else 0)) *
          ∏ i ∈ Γ, ν i (Sum.inr ⁻¹' s i) := by
      intro Γ
      rw [Measure.map_apply (measurable_valuesOn Γ) (MeasurableSet.univ_pi hs)]
      by_cases hoff : ∀ i ∉ Γ, Sum.inl () ∈ s i
      · have e : valuesOn Γ ⁻¹' Set.univ.pi s =
            Set.univ.pi fun i : Γ => Sum.inr ⁻¹' s i.1 := by
          ext τ
          simp only [Set.mem_preimage, Set.mem_pi, Set.mem_univ, true_implies]
          constructor
          · intro h i
            have := h i.1
            unfold valuesOn at this
            simpa [i.2] using this
          · intro h i
            unfold valuesOn
            by_cases hi : i ∈ Γ
            · simpa [hi] using h ⟨i, hi⟩
            · simpa [hi] using hoff i hi
        have h1 : (∏ i ∈ Finset.univ \ Γ, (if Sum.inl () ∈ s i then (1 : ENNReal) else 0)) = 1 :=
          Finset.prod_eq_one fun i hi => if_pos (hoff i (by simpa using hi))
        rw [e, Measure.pi_pi, h1, one_mul]
        exact Finset.prod_coe_sort Γ fun i => ν i (Sum.inr ⁻¹' s i)
      · push Not at hoff
        obtain ⟨i, hi, hn⟩ := hoff
        have e : valuesOn Γ ⁻¹' Set.univ.pi s = (∅ : Set (∀ i : Γ, S i)) := by
          ext τ
          simp only [Set.mem_preimage, Set.mem_pi, Set.mem_univ, true_implies, Set.mem_empty_iff_false,
            iff_false, not_forall]
          refine ⟨i, ?_⟩
          unfold valuesOn
          simpa [hi] using hn
        rw [e, measure_empty, Finset.prod_eq_zero (i := i) (by simpa using hi) (if_neg hn), zero_mul]
    simp only [hbox]
    have hi : ∀ i, withNoneMeasure (ν i) (s i) =
        ν i (Sum.inr ⁻¹' s i) + (if Sum.inl () ∈ s i then (1 : ENNReal) else 0) := fun i => by
      rw [withNoneMeasure_apply _ (hs i), add_comm]
    simp only [hi]
    rw [Finset.prod_add]
    simp only [Finset.powerset_univ, mul_comm]
  rw [hsum, lintegral_finsetSum_measure]
  refine Finset.sum_congr rfl fun Γ _ => ?_
  exact lintegral_map hf (measurable_valuesOn Γ)
end YangMills.Construction.TorusLumps
end
