import YangMills.Construction.ClusterExpansionOfAStep.RandomOrderOfBlocks
import Mathlib
set_option autoImplicit false
noncomputable section
namespace YangMills.Construction.BlockOrder
theorem sum_increments_eq_sub {I J : Type} [DecidableEq I] [LinearOrder J] (f : I → J)
    (hf : Function.Injective f) (F : Finset I → ℝ) (s : Finset I) :
    ∑ Y ∈ s, (F (insert Y (s.filter fun i => f i < f Y)) - F (s.filter fun i => f i < f Y)) =
      F s - F ∅ := by
  induction s using Finset.induction_on_max_value f with
  | empty => simp
  | insert a s ha hmax ih =>
    have hlt : ∀ z ∈ s, f z < f a := fun z hz =>
      lt_of_le_of_ne (hmax z hz) fun h => ha (hf h ▸ hz)
    rw [Finset.sum_insert ha]
    have h1 : (insert a s).filter (fun i => f i < f a) = s := by
      ext z
      simp only [Finset.mem_filter, Finset.mem_insert]
      constructor
      · rintro ⟨rfl | h, h2⟩
        · exact absurd h2 (lt_irrefl _)
        · exact h
      · exact fun h => ⟨Or.inr h, hlt z h⟩
    have h2 : ∀ Y ∈ s, (insert a s).filter (fun i => f i < f Y) = s.filter fun i => f i < f Y := by
      intro Y hY
      ext z
      simp only [Finset.mem_filter, Finset.mem_insert]
      constructor
      · rintro ⟨rfl | h, h3⟩
        · exact absurd (hlt Y hY) (not_lt.mpr h3.le)
        · exact ⟨h, h3⟩
      · exact fun ⟨h, h3⟩ => ⟨Or.inr h, h3⟩
    rw [h1, Finset.sum_congr rfl fun Y hY => by rw [h2 Y hY], ih]
    ring
theorem sumIncrementsAlongOrder_holds : SumIncrementsAlongOrder := by
  intro I _ _ F u
  let f : I → ℝ ×ₗ I := fun i => toLex (u i, i)
  have hf : Function.Injective f := fun a b h => by
    have := congrArg (fun z => (ofLex z).2) h
    simpa [f] using this
  have key := sum_increments_eq_sub f hf F Finset.univ
  have hb : ∀ Y, (Finset.univ.filter fun i => f i < f Y) = precedingBlocks u Y := by
    intro Y
    ext i
    simp only [precedingBlocks, Finset.mem_filter, Finset.mem_univ, true_and, f, Prod.Lex.toLex_lt_toLex]
  simpa only [hb] using key
end YangMills.Construction.BlockOrder
end
