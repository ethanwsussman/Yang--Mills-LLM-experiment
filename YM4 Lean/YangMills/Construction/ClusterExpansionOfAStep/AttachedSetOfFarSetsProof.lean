import YangMills.Construction.ClusterExpansionOfAStep.AttachedSetOfFarSets
import YangMills.Construction.ClusterExpansionOfAStep.DistancesAndClasses
import Mathlib
set_option autoImplicit false
noncomputable section
namespace YangMills.Construction.ClusterExpansionOfAStep
theorem attachedUnchangedByFarSets_holds : AttachedUnchangedByFarSets := by
  classical
  intro n L _ _ r bad Δb Yt ΔY C h0 hfar
  set A₀ := bad.image Prod.fst ∪ Yt ∪ TorusLumps.sitesInBlocks L C with hA₀
  set Big := (bad ∪ Δb).image Prod.fst ∪ (Yt ∪ ΔY) ∪ TorusLumps.sitesInBlocks L C with hBig
  have hsub : A₀ ⊆ Big := by
    intro z hz
    simp only [hA₀, hBig, Finset.mem_union, Finset.mem_image] at hz ⊢
    rcases hz with (⟨b, hb, rfl⟩ | hz) | hz
    · exact Or.inl (Or.inl ⟨b, Or.inl hb, rfl⟩)
    · exact Or.inl (Or.inr (Or.inl hz))
    · exact Or.inr hz
  have hsplit : ∀ z ∈ Big, z ∈ A₀ ∨ z ∈ Δb.image Prod.fst ∪ ΔY := by
    intro z hz
    simp only [hA₀, hBig, Finset.mem_union, Finset.mem_image] at hz ⊢
    rcases hz with (⟨b, hb | hb, rfl⟩ | hz | hz) | hz
    · exact Or.inl (Or.inl (Or.inl ⟨b, hb, rfl⟩))
    · exact Or.inr (Or.inl ⟨b, hb, rfl⟩)
    · exact Or.inl (Or.inl (Or.inr hz))
    · exact Or.inr (Or.inr hz)
    · exact Or.inl (Or.inr hz)
  ext z
  unfold TorusLumps.attachedSites TorusLumps.clusterComponents
  simp only [Finset.mem_biUnion, Finset.mem_filter, id]
  constructor
  · rintro ⟨X, ⟨hX, ⟨w, hw⟩⟩, hz⟩
    have hwX := (Finset.mem_inter.mp hw).1
    have hwC := (Finset.mem_inter.mp hw).2
    have hJ : TorusLumps.ChainConnected (10 * r) Big w z :=
      TorusLumps.chainConnected_of_mem_chainComponents hX hwX hz
    have : ∀ u, TorusLumps.ChainConnected (10 * r) Big w u → u ∈ A₀ := by
      intro u hu
      induction hu with
      | refl => exact Finset.mem_union_right _ hwC
      | tail _ hs ih =>
        rcases hsplit _ hs.2.1 with h | h
        · exact h
        · have := hfar _ h _ ih
          have h2 := hs.2.2
          rw [TorusFields.supDist_comm] at h2
          omega
    exact this z hJ
  · intro hz
    rcases Finset.mem_union.mp hz with hS | hC
    · have := h0 hS
      unfold TorusLumps.attachedSites TorusLumps.clusterComponents at this
      simp only [Finset.mem_biUnion, Finset.mem_filter, id] at this
      obtain ⟨X₀, ⟨hX₀, ⟨w, hw⟩⟩, hzX⟩ := this
      have hwX := (Finset.mem_inter.mp hw).1
      have hwC := (Finset.mem_inter.mp hw).2
      have hJ := TorusLumps.chainConnected_of_mem_chainComponents hX₀ hwX hzX
      have hlift : ∀ u, TorusLumps.ChainConnected (10 * r) A₀ w u →
          TorusLumps.ChainConnected (10 * r) Big w u := by
        intro u hu
        induction hu with
        | refl => exact Relation.ReflTransGen.refl
        | tail _ hs ih => exact Relation.ReflTransGen.tail ih ⟨hsub hs.1, hsub hs.2.1, hs.2.2⟩
      have hJ' : TorusLumps.ChainConnected (10 * r) Big w z := hlift z hJ
      have hzB : z ∈ Big := hsub hz
      obtain ⟨X, hX, hzX'⟩ := TorusLumps.exists_mem_chainComponents (r := 10 * r) hzB
      have hwB : w ∈ Big := hsub (Finset.mem_union_right _ hwC)
      exact ⟨X, ⟨hX, ⟨w, Finset.mem_inter.mpr
        ⟨TorusLumps.mem_of_chainConnected_of_mem_chainComponents hX hzX' hwB
          (TorusLumps.chainConnected_symm hJ'), hwC⟩⟩⟩, hzX'⟩
    · have hzB : z ∈ Big := hsub hz
      obtain ⟨X, hX, hzX⟩ := TorusLumps.exists_mem_chainComponents (r := 10 * r) hzB
      exact ⟨X, ⟨hX, ⟨z, Finset.mem_inter.mpr ⟨hzX, hC⟩⟩⟩, hzX⟩
end YangMills.Construction.ClusterExpansionOfAStep
end
