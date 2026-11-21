import YangMills.Construction.InfiniteLattice.ActionOfTheLatticeIsometriesOnObservablesProof
import YangMills.Construction.InfiniteLattice.CutoffLattice
import YangMills.Construction.InfiniteLattice.FunctionOfASetReadsOnlyItsBonds
import YangMills.Construction.InfiniteLattice.SpaceOfConfigurationsAndWhatAnObservableReadsProof
import YangMills.Construction.InfiniteLattice.WhatAnObservableReads
import Mathlib
set_option autoImplicit false
open MeasureTheory
namespace YangMills.Construction.InfiniteLattice.ReadoutLemmas
open LatticePhases (truncate)
theorem isUnitalStarClosed_boundedMeasurable {Ω : Type*} (m : MeasurableSpace Ω) :
    IsUnitalStarClosed
      {A : Ω → ℂ | Measurable A ∧ ∃ C : ℝ, ∀ ω, ‖A ω‖ ≤ C} where
  add_mem := by
    rintro A ⟨hA, C, hC⟩ B ⟨hB, D, hD⟩
    exact ⟨hA.add hB, C + D, fun ω => (norm_add_le _ _).trans (add_le_add (hC ω) (hD ω))⟩
  mul_mem := by
    rintro A ⟨hA, C, hC⟩ B ⟨hB, D, hD⟩
    refine ⟨hA.mul hB, C * D, fun ω => ?_⟩
    rw [Pi.mul_apply, norm_mul]
    exact mul_le_mul (hC ω) (hD ω) (norm_nonneg _) ((norm_nonneg _).trans (hC ω))
  smul_mem := by
    rintro z A ⟨hA, C, hC⟩
    refine ⟨hA.const_smul z, ‖z‖ * C, fun ω => ?_⟩
    rw [Pi.smul_apply, norm_smul]
    exact mul_le_mul_of_nonneg_left (hC ω) (norm_nonneg _)
  conj_mem := by
    rintro A ⟨hA, C, hC⟩
    exact ⟨Complex.continuous_conj.measurable.comp hA, C, fun ω => by simpa using hC ω⟩
  const_mem z := ⟨measurable_const, ‖z‖, fun _ => le_rfl⟩
section Mesh
variable {a : ℝ}
theorem isUnitalStarClosed_regionObservables (S : Set AmbientSpace) :
    IsUnitalStarClosed (regionObservables a S) := by
  have h₁ := isUnitalStarClosed_boundedMeasurable (inferInstance : MeasurableSpace (GaugeField a))
  have h₂ := isUnitalStarClosed_boundedMeasurable (regionSigma S : MeasurableSpace (GaugeField a))
  refine ⟨fun A hA B hB => ⟨h₁.add_mem A hA.1 B hB.1, (h₂.add_mem A ⟨hA.2, hA.1.2⟩ B ⟨hB.2, hB.1.2⟩).1⟩,
    fun A hA B hB => ⟨h₁.mul_mem A hA.1 B hB.1, (h₂.mul_mem A ⟨hA.2, hA.1.2⟩ B ⟨hB.2, hB.1.2⟩).1⟩,
    fun z A hA => ⟨h₁.smul_mem z A hA.1, (h₂.smul_mem z A ⟨hA.2, hA.1.2⟩).1⟩,
    fun A hA => ⟨h₁.conj_mem A hA.1, (h₂.conj_mem A ⟨hA.2, hA.1.2⟩).1⟩,
    fun z => ⟨h₁.const_mem z, (h₂.const_mem z).1⟩⟩
theorem regionObservables_mono {S S' : Set AmbientSpace} (h : S ⊆ S') :
    regionObservables a S ⊆ regionObservables a S' := by apply _root_.YangMills.Construction.InfiniteLattice.SymmetryAction.boundedRegionObservables_mono <;> assumption
theorem truncate_apply_of_mem {S : Set AmbientSpace} {b : Link a} (h : b ∈ linksWithin S)
    (U : GaugeField a) : truncate S U b = U b :=
  if_pos h
theorem truncate_apply_of_not_mem {S : Set AmbientSpace} {b : Link a} (h : b ∉ linksWithin S)
    (U : GaugeField a) : truncate S U b = 1 :=
  if_neg h
theorem continuous_truncate (S : Set AmbientSpace) :
    Continuous (truncate S : GaugeField a → GaugeField a) := by apply _root_.YangMills.Construction.LatticePhases.ObservableRegions.continuous_truncate <;> assumption
theorem measurableSet_preimage_truncate
    (hB : (inferInstance : MeasurableSpace (GaugeField a)) =
      linkSigma (Set.univ : Set (Link a)))
    (S : Set AmbientSpace) {E : Set (GaugeField a)} (hE : MeasurableSet E) :
    MeasurableSet[regionSigma S] (truncate S ⁻¹' E) := by
  have hle : MeasurableSpace.comap (truncate S : GaugeField a → GaugeField a)
      (linkSigma (Set.univ : Set (Link a))) ≤ regionSigma S := by
    rw [linkSigma]
    simp only [MeasurableSpace.comap_iSup, MeasurableSpace.comap_comp]
    refine iSup₂_le fun b _ => ?_
    by_cases h : b ∈ linksWithin S
    · rw [show (fun U : GaugeField a => U b) ∘ truncate S = fun U => U b from
        funext (truncate_apply_of_mem h)]
      exact le_iSup₂_of_le (f := fun b _ =>
        MeasurableSpace.comap (fun U : GaugeField a => U b) inferInstance) b h le_rfl
    · rw [show (fun U : GaugeField a => U b) ∘ truncate S = fun _ => 1 from
        funext (truncate_apply_of_not_mem h)]
      exact (@measurable_const _ _ _ (regionSigma S) _).comap_le
  exact hle _ ⟨E, hB ▸ hE, rfl⟩
theorem eq_comp_truncate_of_reads {S : Set AmbientSpace} {F : GaugeField a → ℂ}
    (h : ∀ U U' : GaugeField a, (∀ b : Link a, b.LiesIn S → U b = U' b) → F U = F U') :
    F = F ∘ truncate S :=
  funext fun U => h U _ fun _ hb => (truncate_apply_of_mem hb U).symm
theorem mem_regionObservables_of_eq_comp_truncate
    (hB : (inferInstance : MeasurableSpace (GaugeField a)) =
      linkSigma (Set.univ : Set (Link a)))
    {S : Set AmbientSpace} {F : GaugeField a → ℂ} (hF : IsBoundedObservable F)
    (h : F = F ∘ truncate S) :
    F ∈ regionObservables a S := by
  refine ⟨hF, fun E hE => ?_⟩
  have hpre : F ⁻¹' E = truncate S ⁻¹' (F ⁻¹' E) := by
    conv_lhs => rw [h, Set.preimage_comp]
  rw [hpre]
  exact measurableSet_preimage_truncate hB S (hF.1 hE)
theorem truncate_truncate (S₁ S₂ : Set AmbientSpace) (U : GaugeField a) :
    truncate S₂ (truncate S₁ U) = truncate (S₁ ∩ S₂) U := by
  refine Subtype.ext (funext fun b => ?_)
  show truncate S₂ (truncate S₁ U) b = truncate (S₁ ∩ S₂) U b
  by_cases h₂ : b ∈ linksWithin S₂
  · by_cases h₁ : b ∈ linksWithin S₁
    · have h : b ∈ linksWithin (S₁ ∩ S₂) := ⟨⟨h₁.1, h₂.1⟩, ⟨h₁.2, h₂.2⟩⟩
      rw [truncate_apply_of_mem h₂, truncate_apply_of_mem h₁, truncate_apply_of_mem h]
    · have h : b ∉ linksWithin (S₁ ∩ S₂) := fun h => h₁ ⟨h.1.1, h.2.1⟩
      rw [truncate_apply_of_mem h₂, truncate_apply_of_not_mem h₁, truncate_apply_of_not_mem h]
  · have h : b ∉ linksWithin (S₁ ∩ S₂) := fun h => h₂ ⟨h.1.2, h.2.2⟩
    rw [truncate_apply_of_not_mem h₂, truncate_apply_of_not_mem h]
theorem regionObservables_inter (ha : 0 < a) (hR : RegionObservableReadsInteriorLinks)
    (hB : (inferInstance : MeasurableSpace (GaugeField a)) =
      linkSigma (Set.univ : Set (Link a)))
    (S₁ S₂ : Set AmbientSpace) :
    regionObservables a S₁ ∩ regionObservables a S₂ = regionObservables a (S₁ ∩ S₂) := by
  refine Set.Subset.antisymm (fun F hF => ?_) fun F hF =>
    ⟨regionObservables_mono Set.inter_subset_left hF,
      regionObservables_mono Set.inter_subset_right hF⟩
  have e₁ : F = F ∘ truncate S₁ := eq_comp_truncate_of_reads (hR a ha S₁ F hF.1)
  have e₂ : F = F ∘ truncate S₂ := eq_comp_truncate_of_reads (hR a ha S₂ F hF.2)
  refine mem_regionObservables_of_eq_comp_truncate hB hF.1.1 (funext fun U => ?_)
  calc F U = F (truncate S₁ U) := congrFun e₁ U
    _ = F (truncate S₂ (truncate S₁ U)) := congrFun e₂ _
    _ = (F ∘ truncate (S₁ ∩ S₂)) U := by rw [truncate_truncate]; rfl
theorem regionObservables_univ
    (hB : (inferInstance : MeasurableSpace (GaugeField a)) =
      linkSigma (Set.univ : Set (Link a))) :
    regionObservables a Set.univ = {F | IsBoundedObservable F} := by
  have e : (linksWithin Set.univ : Set (Link a)) = Set.univ :=
    Set.eq_univ_of_forall fun _ => ⟨Set.mem_univ _, Set.mem_univ _⟩
  refine Set.Subset.antisymm (fun F hF => hF.1) fun F hF => ⟨hF, ?_⟩
  show Measurable[linkSigma (linksWithin Set.univ)] F
  rw [e, ← hB]
  exact hF.1
end Mesh
theorem isUnitalStarClosed_cutoffLocalRegionObservables (L K : ℕ) (S : Set AmbientSpace) :
    IsUnitalStarClosed (cutoffLocalRegionObservables L K S) := by
  have hc : ∀ T : Set AmbientSpace,
      IsUnitalStarClosed (cutoffRegionObservables L K T) :=
    fun T => isUnitalStarClosed_regionObservables T
  have two : ∀ A ∈ cutoffLocalRegionObservables L K S,
      ∀ B ∈ cutoffLocalRegionObservables L K S, ∃ T : Set AmbientSpace, T ⊆ S ∧
        Bornology.IsBounded T ∧ A ∈ cutoffRegionObservables L K T ∧
          B ∈ cutoffRegionObservables L K T := by
    intro A hA B hB
    obtain ⟨S₁, h₁, b₁, hA⟩ := (mem_cutoffLocalRegionObservables_iff L K S A).1 hA
    obtain ⟨S₂, h₂, b₂, hB⟩ := (mem_cutoffLocalRegionObservables_iff L K S B).1 hB
    exact ⟨S₁ ∪ S₂, Set.union_subset h₁ h₂, b₁.union b₂,
      regionObservables_mono Set.subset_union_left hA,
      regionObservables_mono Set.subset_union_right hB⟩
  refine ⟨fun A hA B hB => ?_, fun A hA B hB => ?_, fun z A hA => ?_, fun A hA => ?_, fun z => ?_⟩
  · obtain ⟨T, hT, hb, hA, hB⟩ := two A hA B hB
    exact (mem_cutoffLocalRegionObservables_iff L K S _).2 ⟨T, hT, hb, (hc T).add_mem A hA B hB⟩
  · obtain ⟨T, hT, hb, hA, hB⟩ := two A hA B hB
    exact (mem_cutoffLocalRegionObservables_iff L K S _).2 ⟨T, hT, hb, (hc T).mul_mem A hA B hB⟩
  · obtain ⟨T, hT, hb, hA⟩ := (mem_cutoffLocalRegionObservables_iff L K S A).1 hA
    exact (mem_cutoffLocalRegionObservables_iff L K S _).2 ⟨T, hT, hb, (hc T).smul_mem z A hA⟩
  · obtain ⟨T, hT, hb, hA⟩ := (mem_cutoffLocalRegionObservables_iff L K S A).1 hA
    exact (mem_cutoffLocalRegionObservables_iff L K S _).2 ⟨T, hT, hb, (hc T).conj_mem A hA⟩
  · exact (mem_cutoffLocalRegionObservables_iff L K S _).2
      ⟨∅, Set.empty_subset S, Bornology.isBounded_empty, (hc ∅).const_mem z⟩
theorem cutoffLocalRegionObservables_mono (L K : ℕ) {S S' : Set AmbientSpace} (h : S ⊆ S') :
    cutoffLocalRegionObservables L K S ⊆ cutoffLocalRegionObservables L K S' := by
  intro F hF
  obtain ⟨T, hT, hb, hF⟩ := (mem_cutoffLocalRegionObservables_iff L K S F).1 hF
  exact (mem_cutoffLocalRegionObservables_iff L K S' F).2 ⟨T, hT.trans h, hb, hF⟩
theorem cutoffLocalRegionObservables_subset (L K : ℕ) (S : Set AmbientSpace) :
    cutoffLocalRegionObservables L K S ⊆ cutoffRegionObservables L K S := by
  intro F hF
  obtain ⟨T, hT, -, hF⟩ := (mem_cutoffLocalRegionObservables_iff L K S F).1 hF
  exact regionObservables_mono hT hF
theorem meshSize_pos {L : ℕ} (hL : Conventions.IsAdmissibleBlockingFactor L) (K : ℕ) :
    0 < PeriodicLattice.meshSize L (K : ℤ) := by apply _root_.YangMills.Construction.CutoffLattice.spacingAt_pos <;> assumption
theorem regionReadout_summary (hR : RegionObservableReadsInteriorLinks)
    (hS : CutoffStructure.FieldSpaceAndSymmetries) : RegionReadout.Summary := by
  intro L K hL _
  have ha := meshSize_pos hL K
  obtain ⟨-, -, -, -, -, -, -, -, hB, -⟩ := (hS _ ha).1
  refine ⟨fun S => ⟨continuous_truncate S, fun F hF => ?_⟩, ⟨fun S =>
    ⟨isUnitalStarClosed_regionObservables S, isUnitalStarClosed_cutoffLocalRegionObservables L K S⟩,
    fun S S' h => ⟨regionObservables_mono h, cutoffLocalRegionObservables_mono L K h⟩,
    cutoffLocalRegionObservables_subset L K,
    regionObservables_univ hB⟩, fun S₁ S₂ => regionObservables_inter ha hR hB S₁ S₂,
    fun S => ⟨?_, ?_⟩⟩
  · tfae_have 1 → 2 := fun h => hR _ ha S F h
    tfae_have 2 → 3 := eq_comp_truncate_of_reads
    tfae_have 3 → 1 := mem_regionObservables_of_eq_comp_truncate hB hF
    tfae_finish
  · refine Set.Subset.antisymm (fun F hF => ?_) ?_
    · obtain ⟨T, hT, hb, hF⟩ := (mem_cutoffLocalRegionObservables_iff L K S F).1 hF
      exact ⟨hF.1, ⟨T, hb, hF.2⟩, (regionObservables_mono hT hF).2⟩
    · rintro F ⟨hO, ⟨Q, hb, hQ⟩, hM⟩
      refine (mem_cutoffLocalRegionObservables_iff L K S F).2
        ⟨S ∩ Q, Set.inter_subset_left, hb.subset Set.inter_subset_right, ?_⟩
      exact (regionObservables_inter ha hR hB S Q).subset ⟨⟨hO, hM⟩, ⟨hO, hQ⟩⟩
  · exact cutoffLocalRegionObservables_eq_localRegionObservables L K S
end YangMills.Construction.InfiniteLattice.ReadoutLemmas
