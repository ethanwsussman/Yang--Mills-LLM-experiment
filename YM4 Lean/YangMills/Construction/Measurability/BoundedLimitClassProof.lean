import YangMills.Construction.Measurability.BoundedLimitClassStatement
import Mathlib
set_option autoImplicit false
open Filter Topology MeasureTheory
open scoped NNReal
namespace YangMills.Construction.Measurability.BoundedLimitClass
variable {X : Type} [MetricSpace X] [MeasurableSpace X] [BorelSpace X]
  {𝔉 : Submodule ℂ (X → ℂ)}
omit [BorelSpace X] in
lemma indicator_one_mem_of_isClosed (h : IsBoundedLimitClosed 𝔉) {F : Set X} (hF : IsClosed F) :
    F.indicator (fun _ => (1 : ℂ)) ∈ 𝔉 := by
  have hb : ∀ (n : ℕ) (x : X), ‖(((hF.apprSeq n x : ℝ≥0) : ℝ) : ℂ)‖ ≤ 1 := by
    intro n x
    rw [Complex.norm_real, Real.norm_eq_abs, NNReal.abs_eq]
    exact_mod_cast HasOuterApproxClosed.apprSeq_apply_le_one hF n x
  refine h.limit_mem (fun n x => (((hF.apprSeq n x : ℝ≥0) : ℝ) : ℂ)) _ (fun n => ?_)
    ⟨1, hb⟩ (fun x => ?_)
  · refine h.continuous_mem _ ?_ ⟨1, hb n⟩
    exact Complex.continuous_ofReal.comp (NNReal.continuous_coe.comp (hF.apprSeq n).continuous)
  · have h1 := tendsto_pi_nhds.1 (HasOuterApproxClosed.tendsto_apprSeq hF) x
    have h2 := ((Complex.continuous_ofReal.comp NNReal.continuous_coe).tendsto _).comp h1
    have he : (Complex.ofReal ∘ NNReal.toReal) (F.indicator (fun _ => (1 : ℝ≥0)) x) =
        F.indicator (fun _ => (1 : ℂ)) x := by
      by_cases hx : x ∈ F <;> simp [hx]
    rw [he] at h2
    exact h2
lemma indicator_one_mem_of_measurableSet (h : IsBoundedLimitClosed 𝔉) {s : Set X}
    (hs : MeasurableSet s) : s.indicator (fun _ => (1 : ℂ)) ∈ 𝔉 := by
  have hone : (fun _ : X => (1 : ℂ)) ∈ 𝔉 := h.continuous_mem _ continuous_const ⟨1, by simp⟩
  have hcompl : ∀ t : Set X, t.indicator (fun _ => (1 : ℂ)) ∈ 𝔉 →
      tᶜ.indicator (fun _ => (1 : ℂ)) ∈ 𝔉 := by
    intro t ht
    have he : tᶜ.indicator (fun _ => (1 : ℂ)) =
        (fun _ : X => (1 : ℂ)) - t.indicator (fun _ => (1 : ℂ)) := by
      ext x
      by_cases hx : x ∈ t <;> simp [hx]
    rw [he]
    exact 𝔉.sub_mem hone ht
  induction s, hs using MeasurableSet.induction_on_open with
  | isOpen U hU =>
    have := hcompl _ (indicator_one_mem_of_isClosed h hU.isClosed_compl)
    rwa [compl_compl] at this
  | compl t _ ih => exact hcompl t ih
  | iUnion f hd _ ih =>
    have hsum : ∀ n : ℕ, (⋃ i ∈ Finset.range n, f i).indicator (fun _ => (1 : ℂ)) =
        ∑ i ∈ Finset.range n, (f i).indicator (fun _ => (1 : ℂ)) := by
      intro n
      ext x
      rw [Finset.sum_apply]
      exact Finset.indicator_biUnion_apply (Finset.range n) f
        (fun i _ j _ hij => hd hij) x
    refine h.limit_mem (fun n => (⋃ i ∈ Finset.range n, f i).indicator (fun _ => (1 : ℂ))) _
      (fun n => ?_) ⟨1, fun n x => ?_⟩ (fun x => ?_)
    · rw [hsum n]
      exact 𝔉.sum_mem (fun i _ => ih i)
    · by_cases hx : x ∈ ⋃ i ∈ Finset.range n, f i <;> simp only [Set.indicator, hx] <;> simp
    · exact ((tendsto_indicator_biUnion_finset f _ x).comp tendsto_finset_range).mono_right
        (pure_le_nhds _)
lemma simpleFunc_mem_of_closed (h : IsBoundedLimitClosed 𝔉) (g : SimpleFunc X ℂ) :
    (g : X → ℂ) ∈ 𝔉 := by
  induction g using SimpleFunc.induction with
  | @const c s hs =>
    have he : (SimpleFunc.piecewise s hs (SimpleFunc.const X c) (SimpleFunc.const X 0) : X → ℂ) =
        c • s.indicator (fun _ => (1 : ℂ)) := by
      ext x
      by_cases hx : x ∈ s <;> simp [hx]
    rw [he]
    exact 𝔉.smul_mem c (indicator_one_mem_of_measurableSet h hs)
  | @add f g _ hf hg =>
    rw [SimpleFunc.coe_add]
    exact 𝔉.add_mem hf hg
theorem claim_holds : Claim := by
  intro X _ _ _ 𝔉 h
  ext f
  constructor
  · exact h.boundedMeasurable f
  · rintro ⟨hm, C, hC⟩
    have hs : StronglyMeasurable f := hm.stronglyMeasurable
    have hC' : ∀ x, ‖f x‖ ≤ max C 0 := fun x => (hC x).trans (le_max_left _ _)
    exact h.limit_mem (fun n => hs.approxBounded (max C 0) n) f
      (fun n => simpleFunc_mem_of_closed h _)
      ⟨max C 0, fun n x => hs.norm_approxBounded_le (le_max_right _ _) n x⟩
      (fun x => hs.tendsto_approxBounded_of_norm_le (hC' x))
end YangMills.Construction.Measurability.BoundedLimitClass
