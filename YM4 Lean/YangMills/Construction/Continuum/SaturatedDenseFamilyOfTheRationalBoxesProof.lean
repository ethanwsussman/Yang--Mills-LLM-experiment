import YangMills.Construction.Continuum.SaturatedDenseFamilyOfTheRationalBoxes
import Mathlib
set_option autoImplicit false
open Set
namespace YangMills.Construction.Continuum.RationalBoxes
theorem exists_isSaturatedDenseInvariant (s : Conventions.StandingParameters)
    (hc : boxUnions.Countable)
    {E : boxUnions → Set ((Fin 4 → ℝ) → ℝ)} (hE : IsDenseInvariantFamily s E) :
    ∃ D, IsSaturatedDenseInvariant s D := by
  obtain ⟨f, hf⟩ : ∃ f, f = ⋃ Q, E Q := ⟨_, rfl⟩
  have hfc : f.Countable := by
    have : Countable boxUnions := hc.to_subtype
    rw [hf]
    exact countable_iUnion hE.countable
  have hsub : ∀ Q, E Q ⊆ f ∩ c1Off Q := fun Q _ hx =>
    ⟨hf ▸ mem_iUnion.2 ⟨Q, hx⟩, hE.sub Q hx⟩
  have hunion : (⋃ Q : boxUnions, f ∩ c1Off Q) = f := by
    refine Subset.antisymm (iUnion_subset fun Q => inter_subset_left) ?_
    rw [hf]
    exact iUnion_subset fun Q _ hx => mem_iUnion.2 ⟨Q, hf ▸ hsub Q hx⟩
  refine ⟨fun Q => f ∩ c1Off Q,
    ⟨fun Q => inter_subset_right, fun Q => hfc.mono inter_subset_left, ?_, ?_, ?_⟩, ?_⟩
  · intro Q g hg ε hε
    obtain ⟨h, hh, hlt⟩ := hE.dense Q g hg ε hε
    exact ⟨h, hsub Q hh, hlt⟩
  · intro w hw g hg
    simp only [hunion] at hg ⊢
    rw [hf] at hg ⊢
    exact hE.invariant_hyperoctahedral w hw g hg
  · intro v hv g hg
    simp only [hunion] at hg ⊢
    rw [hf] at hg ⊢
    exact hE.invariant_shift v hv g hg
  · intro Q
    simp only [hunion]
theorem chosenFamilyIsSaturatedDense_of_claim (h : BoxSpaceProperties.Claim) :
    ChosenFamilyIsSaturatedDense := by
  intro s
  have hb := h s 1 le_rfl
  obtain ⟨E, hE⟩ := hb.exists_denseInvariant
  exact Classical.epsilon_spec (exists_isSaturatedDenseInvariant s hb.boxes_countable hE)
end YangMills.Construction.Continuum.RationalBoxes
