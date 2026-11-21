import YangMills.Construction.Lattice.ComplexAverageReadsTheDoubleBlock
import YangMills.Construction.Lattice.ComplexObjectsReadTheBondsOfADoubleBlock
import YangMills.Construction.Lattice.PropertiesOfTheTwoSchemes
import Mathlib
set_option autoImplicit false
open Set
noncomputable section
namespace YangMills.Construction.PeriodicLattice
variable {L m K k : ℕ}
private theorem contourHolonomies_eq_of_eqOn_bondsInDoubleBlock {c : BondAtLevel L m K (k + 1)}
    {y : SiteAtLevel L m K (k + 1)} (hy : y ∈ ({c.source, c.target} : Set (SiteAtLevel L m K (k + 1))))
    {x : SiteAtLevel L m K k} (hpaths : BlockPathProperties y x)
    {V W : BondAtLevel L m K k → Matrices.ComplexMatrix2}
    (h : ∀ b ∈ (bondsInDoubleBlock c : Set (BondAtLevel L m K k)), V b = W b) :
    contourHolonomies V y x = contourHolonomies W y x := by
  have hsub : unitBlock y ⊆ bondDoubleBlock c := by
    rcases hy with rfl | hy
    · exact subset_union_left
    · rw [mem_singleton_iff.1 hy]
      exact subset_union_right
  funext σ
  simp only [contourHolonomies, pathHolonomy]
  congr 1
  refine List.map_congr_left fun b hb => h b ?_
  obtain ⟨h₁, h₂⟩ := (hpaths.contour_within σ).2 b hb
  exact ⟨hsub h₁, hsub h₂⟩
private theorem opposite_mem_bondsInDoubleBlock {c : BondAtLevel L m K (k + 1)}
    {b : BondAtLevel L m K k} (hb : b ∈ (bondsInDoubleBlock c : Set (BondAtLevel L m K k))) :
    b.opposite ∈ (bondsInDoubleBlock c : Set (BondAtLevel L m K k)) :=
  ⟨hb.2, hb.1⟩
private theorem mem_complexAveragingDomain_of_eqOn {c : BondAtLevel L m K (k + 1)}
    (hpaths : ∀ y ∈ ({c.source, c.target} : Set (SiteAtLevel L m K (k + 1))),
      ∀ x ∈ sitesInBlock (levelDepth K k) y, BlockPathProperties y x)
    {V W : BondAtLevel L m K k → Matrices.ComplexMatrix2}
    (h : ∀ b ∈ (bondsInDoubleBlock c : Set (BondAtLevel L m K k)), V b = W b)
    (hV : V ∈ complexAveragingDomain c) : W ∈ complexAveragingDomain c := by
  obtain ⟨hfield, hsrc, htgt⟩ := hV
  refine ⟨⟨fun b hb => ?_, fun b hb => ?_⟩, fun x hx => ?_, fun x hx => ?_⟩
  · rw [← h b hb]
    exact hfield.1 b hb
  · rw [← h b hb, ← h _ (opposite_mem_bondsInDoubleBlock hb)]
    exact hfield.2 b hb
  · have hy : c.source ∈ ({c.source, c.target} : Set (SiteAtLevel L m K (k + 1))) := Or.inl rfl
    rw [← contourHolonomies_eq_of_eqOn_bondsInDoubleBlock hy (hpaths _ hy x hx) h]
    exact hsrc x hx
  · have hy : c.target ∈ ({c.source, c.target} : Set (SiteAtLevel L m K (k + 1))) := Or.inr rfl
    rw [← contourHolonomies_eq_of_eqOn_bondsInDoubleBlock hy (hpaths _ hy x hx) h]
    exact htgt x hx
theorem complexDataDeterminedOnDoubleBlock_holds
    (hschemes : AveragingSchemeProperties)
    (hlocal : ComplexAverageIsLocal) :
    ComplexDataDeterminedOnDoubleBlock := by
  intro L hL m K k hm hk c hc V W h
  have hpaths : ∀ y ∈ ({c.source, c.target} : Set (SiteAtLevel L m K (k + 1))),
      ∀ x ∈ sitesInBlock (levelDepth K k) y, BlockPathProperties y x := by
    intro y _ x hx
    exact ((hschemes L hL m K k hm hk .centred).1 y x hx).1
  have hR := hlocal L m K k hL.1 hL.2 hm hk c hc
  have h' : ∀ b ∈ (bondsInDoubleBlock c : Set (BondAtLevel L m K k)), W b = V b :=
    fun b hb => (h b hb).symm
  refine ⟨⟨mem_complexAveragingDomain_of_eqOn hpaths h, mem_complexAveragingDomain_of_eqOn hpaths h'⟩,
    hR.mem_domain_iff V W h, ?_, ?_, ?_⟩
  · unfold complexBlockAverage
    rw [if_pos hc, if_pos hc]
    exact hR.average_eq V W h
  · intro y hy x hx
    simp only [complexMeanContourHolonomy]
    rw [contourHolonomies_eq_of_eqOn_bondsInDoubleBlock hy (hpaths y hy x hx) h]
  · intro B B' hB b hb
    unfold expTwist
    by_cases hp : b.IsPositivelyOriented
    · rw [if_pos hp, if_pos hp, hB b hb, h b hb]
    · have hr := opposite_mem_bondsInDoubleBlock hb
      rw [if_neg hp, if_neg hp, hB _ hr, h _ hr]
end YangMills.Construction.PeriodicLattice
end
