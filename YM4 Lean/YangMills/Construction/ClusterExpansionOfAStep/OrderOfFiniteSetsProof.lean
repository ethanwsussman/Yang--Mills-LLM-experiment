import YangMills.Construction.ClusterExpansionOfAStep.OrderOfFiniteSets
import Mathlib
set_option autoImplicit false
noncomputable section
open MeasureTheory
namespace YangMills.Construction.RandomOrder
theorem integrableOfLowerRankSet_holds : IntegrableOfLowerRankSet := by
  intro K _ k₀ p
  classical
  letI : MeasurableSpace (Finset K) := ⊤
  have hmem : ∀ i : K, MeasurableSet {v : K → ℝ | v i < v k₀} := fun i =>
    measurableSet_lt (measurable_pi_apply i) (measurable_pi_apply k₀)
  have hm : Measurable fun v : K → ℝ => Finset.univ.filter fun k => v k < v k₀ := by
    refine measurable_to_countable' fun A => ?_
    have : (fun v : K → ℝ => Finset.univ.filter fun k => v k < v k₀) ⁻¹' {A} =
        ⋂ i, {v | v i < v k₀ ↔ i ∈ A} := by
      ext v
      simp only [Set.mem_preimage, Set.mem_singleton_iff, Set.mem_iInter, Set.mem_setOf_eq, Finset.ext_iff,
        Finset.mem_filter, Finset.mem_univ, true_and]
    rw [this]
    refine MeasurableSet.iInter fun i => ?_
    by_cases hi : i ∈ A
    · have : {v : K → ℝ | v i < v k₀ ↔ i ∈ A} = {v | v i < v k₀} := by
        ext v
        simp [hi]
      rw [this]
      exact hmem i
    · have : {v : K → ℝ | v i < v k₀ ↔ i ∈ A} = {v | v i < v k₀}ᶜ := by
        ext v
        simp [hi]
      rw [this]
      exact (hmem i).compl
  have hf : Measurable fun v : K → ℝ => p (Finset.univ.filter fun k => v k < v k₀) :=
    (measurable_from_top (f := p)).comp hm
  refine Integrable.of_bound hf.aestronglyMeasurable
    (∑ A : Finset K, |p A|) (Filter.Eventually.of_forall fun v => ?_)
  rw [Real.norm_eq_abs]
  exact Finset.single_le_sum (f := fun A => |p A|) (fun _ _ => abs_nonneg _) (Finset.mem_univ _)
end YangMills.Construction.RandomOrder
end
