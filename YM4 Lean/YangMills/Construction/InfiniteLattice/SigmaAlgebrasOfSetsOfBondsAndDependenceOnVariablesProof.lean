import YangMills.Construction.InfiniteLattice.MeasurabilityIsDependenceOnVariablesAtEverySpacing
import YangMills.Construction.InfiniteLattice.SigmaAlgebrasOfSetsOfBondsAndDependenceOnVariables
import YangMills.Construction.InfiniteLattice.StatesFunctionsAndTheWeakTopologyOfOneLattice
import Mathlib
noncomputable section
namespace YangMills.Construction.InfiniteLattice.LinkSigmaProof
variable {a : ℝ}
def spliceFamily (𝓜 : Set (Link a)) (U U' : GaugeField a) :
    positiveLinks a → Matrices.ComplexMatrix2.specialUnitary :=
  open Classical in fun c => if c.1 ∈ 𝓜 then U c.1 else U' c.1
def splice (ha : 0 < a) (𝓜 : Set (Link a)) (U U' : GaugeField a) : GaugeField a :=
  gaugeFieldOfPositive ha (spliceFamily 𝓜 U U')
theorem splice_apply (ha : 0 < a) (𝓜 : Set (Link a)) (U U' : GaugeField a)
    (b : Link a) : splice ha 𝓜 U U' b = extendFromPositive (spliceFamily 𝓜 U U') b := rfl
theorem splice_of_mem (ha : 0 < a) {𝓜 : Set (Link a)} (U U' : GaugeField a)
    {b : Link a} (hp : b ∈ positiveLinks a) (hb : b ∈ 𝓜) : splice ha 𝓜 U U' b = U b := by
  rw [splice_apply, extendFromPositive, dif_pos hp, spliceFamily]
  exact if_pos hb
theorem splice_of_not_mem (ha : 0 < a) {𝓜 : Set (Link a)} (U U' : GaugeField a)
    {b : Link a} (hp : b ∈ positiveLinks a) (hb : b ∉ 𝓜) :
    splice ha 𝓜 U U' b = U' b := by
  rw [splice_apply, extendFromPositive, dif_pos hp, spliceFamily]
  exact if_neg hb
theorem dependsOnlyOn_inter (ha : 0 < a) {𝓜 𝓜' : Set (Link a)} (h𝓜 : IsLinkSet 𝓜)
    (h𝓜' : IsLinkSet 𝓜') {F : GaugeField a → ℂ} (hF : DependsOnlyOn 𝓜 F)
    (hF' : DependsOnlyOn 𝓜' F) : DependsOnlyOn (𝓜 ∩ 𝓜') F := by
  intro U U' hUU'
  refine (hF U (splice ha 𝓜 U U') fun b hb => ?_).trans
    (hF' (splice ha 𝓜 U U') U' fun b hb => ?_)
  · exact (splice_of_mem ha U U' (h𝓜 hb) hb).symm
  · by_cases hm : b ∈ 𝓜
    · rw [splice_of_mem ha U U' (h𝓜 hm) hm]
      exact hUU' b ⟨hm, hb⟩
    · exact splice_of_not_mem ha U U' (h𝓜' hb) hm
theorem linksInside_eq (S : Set AmbientSpace) :
    linksInside a S = positiveLinksWithin a S := by
  ext b
  simp [linksInside, positiveLinksWithin, ← positiveLinks_eq_self, LinksLieIn, linksWithin]
  tauto
theorem linksInside_inter (S S' : Set AmbientSpace) :
    linksInside a S ∩ linksInside a S' = linksInside a (S ∩ S') := by
  ext b
  simp only [linksInside, LinksLieIn, Set.mem_inter_iff, Set.mem_ofPred_eq,
    Set.mem_singleton_iff, forall_eq]
  tauto
theorem linkSigmaAndDependence_holds (measurability : MeasurableIffDependsOnlyAllSpacings) :
    LinkSigmaAndDependence := by
  intro a ha
  obtain ⟨hmeas, hsigma, -, -⟩ := measurability a ha
  have hlinks : ∀ S : Set AmbientSpace, IsLinkSet (linksInside a S) := fun S b hb => hb.1
  refine ⟨fun 𝓜 𝓜' h𝓜 h𝓜' F hF => ⟨hmeas 𝓜 F h𝓜 hF, dependsOnlyOn_inter ha h𝓜 h𝓜'⟩, fun S => ?_,
    fun S S' F hF hS hS' => ?_⟩
  · ext F
    simp only [regionObservables, IsRegionMeasurable, Set.mem_ofPred_eq]
    rw [hsigma, linksInside_eq]
  · have key : ∀ T : Set AmbientSpace,
        IsRegionMeasurable T F ↔ DependsOnlyOn (linksInside a T) F := fun T => by
      rw [← hmeas _ F (hlinks T) hF, IsRegionMeasurable, hsigma]
    rw [key] at hS hS' ⊢
    rw [← linksInside_inter]
    exact dependsOnlyOn_inter ha (hlinks S) (hlinks S') hS hS'
end YangMills.Construction.InfiniteLattice.LinkSigmaProof
end
