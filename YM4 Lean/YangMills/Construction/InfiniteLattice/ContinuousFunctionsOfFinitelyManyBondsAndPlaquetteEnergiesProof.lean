import YangMills.Construction.InfiniteLattice.ContinuousFunctionsOfFinitelyManyBondsAndPlaquetteEnergies
import YangMills.Construction.InfiniteLattice.ElementaryFactsOfBondsSpecificationAndGaugeTransformations
import YangMills.Construction.InfiniteLattice.SpaceOfConfigurationsAndLatticeIsometries
import Mathlib
set_option autoImplicit false
open Set
noncomputable section
namespace YangMills.Construction.InfiniteLattice
theorem subset_linksInside_linkEndpoints {𝓜 : Set (Link (1 : ℝ))} (h𝓜 : IsLinkSet 𝓜) :
    𝓜 ⊆ linksInside 1 (linkEndpoints 𝓜) := by
  intro b hb
  refine ⟨h𝓜 hb, ?_⟩
  intro b' hb'
  have hbb : b' = b := hb'
  subst hbb
  exact ⟨⟨b', hb, Or.inl rfl⟩, ⟨b', hb, Or.inr rfl⟩⟩
theorem continuousLocalAndFaceEnergies_holds
    (hElementary : ElementaryLatticeFacts)
    (hSpace : FieldSpace.SymmetryProperties) :
    ContinuousLocalAndFaceEnergies.Statement := by
  obtain ⟨-, hFaces, -, hLocal, -, -, hMeasurable, -, -⟩ :=
    hElementary 1 1 one_pos one_pos
  have hCompact : CompactSpace (GaugeField (1 : ℝ)) := (hSpace 1 one_pos).1.1
  refine ⟨?_, ?_, ?_⟩
  · intro 𝓜 h𝓜 hfin H hcont hdep
    have hobs : IsBoundedObservable H := by
      obtain ⟨C, hC⟩ := isCompact_univ.exists_bound_of_continuousOn hcont.continuousOn
      exact ⟨hcont.measurable, C, fun U => hC U (mem_univ U)⟩
    have hloc : IsLocalObservable H := (hMeasurable.2.2.2 H hobs).2 ⟨𝓜, h𝓜, hfin, hdep⟩
    refine ⟨⟨hobs, hloc, hcont⟩, ?_, ?_⟩
    · rw [hMeasurable.2.2.1]
      refine ⟨hobs, fun U U' hUU => hdep U U' fun b hb => ?_⟩
      exact hUU b (subset_linksInside_linkEndpoints h𝓜 hb)
    · exact (hLocal.2.2.2.2.2.2.2 H hobs hloc).2.2.2 𝓜 h𝓜 hfin hdep
  · intro p
    obtain ⟨hIcc, -, -, -, hAll, -⟩ := hFaces
    exact ⟨(hAll p).1, (hAll p).2, fun U => hIcc p U⟩
  · intro 𝓛 h𝓛 hfin
    obtain ⟨-, -, -, -, -, hFinite⟩ := hFaces
    have hW := hFinite ⟨hfin.toFinset, fun b hb => h𝓛 (hfin.mem_toFinset.mp hb)⟩
    simpa using hW
end YangMills.Construction.InfiniteLattice
