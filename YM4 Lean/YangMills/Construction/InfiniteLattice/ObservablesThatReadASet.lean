import YangMills.Construction.InfiniteLattice.LinkSupportAndRegionObservables
import YangMills.Construction.InfiniteLattice.ObservablesHypercubicLatticeMapsAndHyperplanes
import YangMills.Construction.InfiniteLattice.PositiveLinksAndCylinderFunctions
import Mathlib
set_option autoImplicit false
noncomputable section
namespace YangMills.Construction.InfiniteLattice
def cutoffRegionObservables (L K : ℕ) (S : Set AmbientSpace) :
    Set (GaugeFieldAtScale L K → ℂ) :=
  regionObservables (PeriodicLattice.meshSize L (K : ℤ)) S
def cutoffLocalRegionObservables (L K : ℕ) (S : Set AmbientSpace) :
    Set (GaugeFieldAtScale L K → ℂ) :=
  boundedSubsetObservables (PeriodicLattice.meshSize L (K : ℤ)) S
theorem mem_cutoffLocalRegionObservables_iff (L K : ℕ) (S : Set AmbientSpace)
    (G : GaugeFieldAtScale L K → ℂ) :
    G ∈ cutoffLocalRegionObservables L K S ↔
      ∃ T : Set AmbientSpace, T ⊆ S ∧ Bornology.IsBounded T ∧ G ∈ cutoffRegionObservables L K T := by
  simp only [cutoffLocalRegionObservables, boundedSubsetObservables, cutoffRegionObservables,
    Set.mem_iUnion, Set.mem_ofPred_eq, exists_prop, and_assoc]
theorem cutoffLocalRegionObservables_eq_localRegionObservables (L K : ℕ) (S : Set AmbientSpace) :
    cutoffLocalRegionObservables L K S =
      localRegionObservables (PeriodicLattice.meshSize L (K : ℤ)) S := by
  ext G
  rw [mem_cutoffLocalRegionObservables_iff]
  simp only [localRegionObservables, Set.mem_iUnion, Set.mem_ofPred_eq, exists_prop]
  constructor
  · rintro ⟨T, hT, hbdd, hG⟩
    refine ⟨T, hbdd, ?_⟩
    rwa [Set.inter_eq_right.mpr hT]
  · rintro ⟨Q, hbdd, hG⟩
    exact ⟨S ∩ Q, Set.inter_subset_left, hbdd.subset Set.inter_subset_right, hG⟩
end YangMills.Construction.InfiniteLattice
