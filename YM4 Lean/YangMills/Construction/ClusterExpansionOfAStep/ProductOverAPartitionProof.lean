import YangMills.Construction.ClusterExpansionOfAStep.ProductOverAPartition
import Mathlib
set_option autoImplicit false
noncomputable section
open MeasureTheory
namespace YangMills.Construction.ProductMeasure
theorem lintegralPiPartition : LintegralPiPartitionStatement := by
  classical
  intro B I Q X T _ _ _ _ _ μ _ e f hf
  set m₁ : Measure (∀ i, T i → X) := Measure.pi fun i : I => Measure.pi fun _ : T i => μ with hm₁
  set m₂ : Measure (Q → X) := Measure.pi fun _ : Q => μ with hm₂
  have ha : Measurable fun p : (∀ i, T i → X) × (Q → X) => glueParts e p.1 p.2 := by
    refine measurable_pi_lambda _ fun b => ?_
    unfold glueParts
    rcases hb : e.symm b with p | u
    · simp only
      exact (measurable_pi_apply p.2).comp ((measurable_pi_apply p.1).comp measurable_fst)
    · simp only
      exact (measurable_pi_apply u).comp measurable_snd
  have hmap : Measure.map (fun p : (∀ i, T i → X) × (Q → X) => glueParts e p.1 p.2) (m₁.prod m₂) =
      Measure.pi fun _ : B => μ := by
    symm
    refine Measure.pi_eq fun s hs => ?_
    rw [Measure.map_apply ha (MeasurableSet.univ_pi hs)]
    have hpre : (fun p : (∀ i, T i → X) × (Q → X) => glueParts e p.1 p.2) ⁻¹' Set.univ.pi s =
        (Set.univ.pi fun i => Set.univ.pi fun t => s (e (Sum.inl ⟨i, t⟩))) ×ˢ
          (Set.univ.pi fun u => s (e (Sum.inr u))) := by
      ext ⟨c, r⟩
      simp only [Set.mem_preimage, Set.mem_pi, Set.mem_univ, true_implies, Set.mem_prod]
      constructor
      · intro h
        refine ⟨fun i t => ?_, fun u => ?_⟩
        · have := h (e (Sum.inl ⟨i, t⟩))
          simpa [glueParts] using this
        · have := h (e (Sum.inr u))
          simpa [glueParts] using this
      · rintro ⟨h1, h2⟩ b
        obtain ⟨x, rfl⟩ := e.surjective b
        rcases x with ⟨i, t⟩ | u
        · simpa [glueParts] using h1 i t
        · simpa [glueParts] using h2 u
    rw [hpre, Measure.prod_prod, hm₁, hm₂, Measure.pi_pi]
    simp only [Measure.pi_pi]
    rw [← Equiv.prod_comp e (fun b => μ (s b)), Fintype.prod_sum_type, Fintype.prod_sigma]
  rw [← hmap, lintegral_map hf ha]
  exact lintegral_prod (fun p : (∀ i, T i → X) × (Q → X) => f (glueParts e p.1 p.2))
    (hf.comp ha).aemeasurable
end YangMills.Construction.ProductMeasure
end
