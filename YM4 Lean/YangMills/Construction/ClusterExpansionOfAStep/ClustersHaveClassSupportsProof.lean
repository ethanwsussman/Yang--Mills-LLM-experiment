import YangMills.Construction.ClusterExpansionOfAStep.ClustersHaveClassSupports
import YangMills.Construction.ClusterExpansionOfAStep.DistancesAndClasses
import Mathlib
set_option autoImplicit false
noncomputable section
namespace YangMills.Construction.TorusLumps
open TorusFields
namespace ClusterSupports
theorem chainConnected_within_component {N : ℕ} [NeZero N] {r : ℕ} {Z X : Finset (TorusSite N)}
    (hX : X ∈ chainComponents r Z)
    {y z : TorusSite N} (hy : y ∈ X) (h : ChainConnected r Z y z) : ChainConnected r X y z := by
  induction h with
  | refl => exact Relation.ReflTransGen.refl
  | @tail b c hb hs ih =>
    have hbX : b ∈ X := mem_of_chainConnected_of_mem_chainComponents hX hy hs.1 hb
    have hcX : c ∈ X := mem_of_chainConnected_of_mem_chainComponents hX hy hs.2.1 (hb.tail hs)
    exact ih.tail ⟨hbX, hcX, hs.2.2⟩
end ClusterSupports
open ClusterSupports in
theorem FreeComponentsAreClusterSupports.holds : FreeComponentsAreClusterSupports := by
  intro n L r _ _ bad Yt C X hX hdis
  classical
  have hsub : X ⊆ bad.image Prod.fst ∪ Yt ∪ sitesInBlocks L C := subset_of_mem_chainComponents hX
  have hsites : clusterSupportSites L (supportOfComponent L bad Yt X) = X := by
    ext z
    simp only [clusterSupportSites, supportOfComponent, Finset.mem_union, Finset.mem_image,
      Finset.mem_filter, Finset.mem_inter]
    constructor
    · rintro (⟨b, ⟨_, hb⟩, rfl⟩ | ⟨_, hz⟩)
      · exact hb
      · exact hz
    · intro hz
      rcases Finset.mem_union.mp (hsub hz) with h | h
      · rcases Finset.mem_union.mp h with h | h
        · obtain ⟨b, hb, rfl⟩ := Finset.mem_image.mp h
          exact Or.inl ⟨b, ⟨hb, hz⟩, rfl⟩
        · exact Or.inr ⟨h, hz⟩
      · exact absurd h (Finset.disjoint_left.mp hdis hz)
  refine ⟨hsites, ?_, ?_⟩
  · rw [hsites]
    obtain ⟨y, hy, rfl⟩ := mem_chainComponents.mp hX
    exact ⟨y, Finset.mem_filter.mpr ⟨hy, Relation.ReflTransGen.refl⟩⟩
  · rw [hsites]
    intro y hy z hz
    exact chainConnected_within_component hX hy (chainConnected_of_mem_chainComponents hX hy hz)
end YangMills.Construction.TorusLumps
end
