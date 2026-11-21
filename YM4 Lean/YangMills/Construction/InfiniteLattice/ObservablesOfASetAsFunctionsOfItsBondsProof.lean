import YangMills.Construction.ChessboardTori.ObservablesMeasurableInASetAndTheirRestrictionToATorusProof
import YangMills.Construction.InfiniteLattice.FunctionsOfASetOfBondsProof
import YangMills.Construction.InfiniteLattice.ObservablesOfASetAsFunctionsOfItsBonds
import YangMills.Construction.InfiniteLattice.PropertiesOfTheWilsonKernelOnObservablesProof
import Mathlib
set_option autoImplicit false
open Set
namespace YangMills.Construction.InfiniteLattice.RegionObservablesProof
open YangMills.Construction.FieldsAtSpacing
variable {a : ℝ}
theorem borel_measurable_of_continuous {X Y : Type*} [TopologicalSpace X] [TopologicalSpace Y]
    {r : X → Y} (hr : Continuous r) : @Measurable X Y (borel X) (borel Y) r := by apply _root_.YangMills.Construction.InfiniteLattice.LinkSetFunctions.continuous_measurable_borel <;> assumption
theorem continuous_linkRestriction (𝓑 : Set (Link a)) :
    Continuous (linkRestriction 𝓑) :=
  continuous_pi fun b => (continuous_apply (b : Link a)).comp continuous_subtype_val
theorem eq_of_eq_on_positiveLinks {S : Set AmbientSpace} {U U' : GaugeField a}
    (e : ∀ b ∈ positiveLinksWithin a S, U b = U' b) {b : Link a}
    (hb : b ∈ (linksWithin S : Set (Link a))) : U b = U' b := by apply _root_.YangMills.Construction.ChessboardTori.MeasurableObservables.eq_on_linksWithin <;> assumption
theorem dependsOnlyOnLinks_iff_forall_eq (L : Set (Link a)) (A : GaugeField a → ℂ) :
    DependsOnlyOnLinks L A ↔ FieldsAtSpacing.DependsOnlyOnLinks L A := by apply _root_.YangMills.Construction.InfiniteLattice.WilsonOperatorPropertiesProof.dependsOnlyOnLinks_iff_fieldsAtSpacing <;> assumption
theorem dependsOnLinks_linksWithin_iff (S : Set AmbientSpace) (A : GaugeField a → ℂ) :
    DependsOnlyOnLinks (linksWithin S) A ↔
      DependsOnlyOnLinks (positiveLinksWithin a S) A := by
  constructor
  · intro h U U' e
    refine h U U' (funext fun b => ?_)
    exact eq_of_eq_on_positiveLinks (U := U) (U' := U') (fun c hc => congrFun e ⟨c, hc⟩) b.2
  · intro h U U' e
    exact h U U' (funext fun b => congrFun e ⟨b.1, b.2.2⟩)
theorem factorsThroughLinks_linksWithin {S : Set AmbientSpace} {A : GaugeField a → ℂ}
    (h : FactorsThroughLinks (positiveLinksWithin a S) A) :
    FactorsThroughLinks (linksWithin S) A := by
  obtain ⟨f, hf, ⟨C, hC⟩, rfl⟩ := h
  let r : LinkVariables (linksWithin S : Set (Link a)) → LinkVariables (positiveLinksWithin a S) :=
    fun g b => g ⟨b.1, b.2.2⟩
  have hr : Continuous r := continuous_pi fun b => continuous_apply _
  exact ⟨f ∘ r, hf.comp (borel_measurable_of_continuous hr), ⟨C, fun g => hC _⟩, rfl⟩
theorem isBoundedObservable_of_factorsThroughLinks {S : Set AmbientSpace} {A : GaugeField a → ℂ}
    (h : FactorsThroughLinks (linksWithin S) A) :
    IsBoundedObservable A ∧ DependsOnlyOnLinks (linksWithin S) A := by
  obtain ⟨f, hf, ⟨C, hC⟩, rfl⟩ := h
  refine ⟨⟨?_, C, fun U => hC _⟩, fun U U' e => ?_⟩
  · exact hf.comp (borel_measurable_of_continuous (continuous_linkRestriction _))
  · have : linkRestriction (linksWithin S) U = linkRestriction (linksWithin S) U' := e
    simp only [Function.comp_apply, this]
theorem regionObservablesAsLinkFunctions_holds (h : LinkFunctionsStatement) :
    RegionObservablesAsLinkFunctions := by
  intro a ha
  have hO := (h a ha ∅ (empty_subset _)).2.2.1
  have mono : ∀ S S' : Set AmbientSpace, S ⊆ S' →
      regionObservables a S ⊆ regionObservables a S' := hO.2.1
  have closed : ∀ S : Set AmbientSpace, IsUnitalStarClosed (regionObservables a S) := fun S => by
    obtain ⟨-, -, ⟨W, hW⟩, hmul, hconj, -⟩ := hO.1 S
    have hmem : ∀ A, A ∈ regionObservables a S ↔ A ∈ W := fun A => by
      change A ∈ boundedRegionObservables a S ↔ _
      rw [← hW]
      rfl
    refine ⟨fun A hA B hB => ?_, hmul, fun z A hA => ?_, hconj, fun z => ?_⟩
    · exact (hmem _).2 (W.add_mem ((hmem _).1 hA) ((hmem _).1 hB))
    · exact (hmem _).2 (W.smul_mem z ((hmem _).1 hA))
    · exact ⟨⟨measurable_const, ‖z‖, fun _ => le_rfl⟩, measurable_const⟩
  have memLocal : ∀ (S : Set AmbientSpace) (A : FieldSpace a → ℂ),
      A ∈ boundedSubsetObservables a S ↔
        ∃ S', (S' ⊆ S ∧ Bornology.IsBounded S') ∧ A ∈ regionObservables a S' := fun S A => by
    simp only [boundedSubsetObservables, mem_iUnion, mem_ofPred_eq, exists_prop]
  have localClosed : ∀ S : Set AmbientSpace,
      IsUnitalStarClosed (boundedSubsetObservables a S) := fun S => by
    refine ⟨fun A hA B hB => ?_, fun A hA B hB => ?_, fun z A hA => ?_, fun A hA => ?_,
      fun z => ?_⟩
    · obtain ⟨S₁, ⟨h₁, b₁⟩, m₁⟩ := (memLocal S A).1 hA
      obtain ⟨S₂, ⟨h₂, b₂⟩, m₂⟩ := (memLocal S B).1 hB
      exact (memLocal S _).2 ⟨S₁ ∪ S₂, ⟨union_subset h₁ h₂, b₁.union b₂⟩,
        (closed _).add_mem _ (mono _ _ subset_union_left m₁) _ (mono _ _ subset_union_right m₂)⟩
    · obtain ⟨S₁, ⟨h₁, b₁⟩, m₁⟩ := (memLocal S A).1 hA
      obtain ⟨S₂, ⟨h₂, b₂⟩, m₂⟩ := (memLocal S B).1 hB
      exact (memLocal S _).2 ⟨S₁ ∪ S₂, ⟨union_subset h₁ h₂, b₁.union b₂⟩,
        (closed _).mul_mem _ (mono _ _ subset_union_left m₁) _ (mono _ _ subset_union_right m₂)⟩
    · obtain ⟨S₁, hb, m₁⟩ := (memLocal S A).1 hA
      exact (memLocal S _).2 ⟨S₁, hb, (closed _).smul_mem z _ m₁⟩
    · obtain ⟨S₁, hb, m₁⟩ := (memLocal S A).1 hA
      exact (memLocal S _).2 ⟨S₁, hb, (closed _).conj_mem _ m₁⟩
    · exact (memLocal S _).2 ⟨∅, ⟨empty_subset _, Bornology.isBounded_empty⟩,
        (closed _).const_mem z⟩
  have forms : ∀ (S : Set AmbientSpace) (A : FieldSpace a → ℂ), IsBoundedObservable A →
      [A ∈ regionObservables a S, FactorsThroughLinks (positiveLinksWithin a S) A,
        DependsOnlyOnLinks (linksWithin S) A].TFAE := fun S A hA => by
    have h₁ := ((h a ha (positiveLinksWithin a S) inter_subset_left).2.1 A hA).1
    have hset := (hO.1 S).2.1
    tfae_have 1 ↔ 3 := by
      rw [dependsOnLinks_linksWithin_iff]
      constructor
      · intro hm
        have hm' : A ∈ boundedRegionObservables a S := hm
        rw [hset] at hm'
        exact (dependsOnlyOnLinks_iff_forall_eq _ _).2 hm'.2.2.1
      · intro hag
        have hag' := (dependsOnlyOnLinks_iff_forall_eq _ _).1 hag
        exact show A ∈ boundedRegionObservables a S from by
          rw [hset]
          exact ⟨hA, (h₁.out 1 0).1 hag', hag', (h₁.out 1 2).1 hag'⟩
    tfae_have 2 ↔ 3 := by
      rw [dependsOnLinks_linksWithin_iff]
      exact (h₁.out 2 1).trans (dependsOnlyOnLinks_iff_forall_eq _ _).symm
    tfae_finish
  refine ⟨fun S => ⟨closed S, localClosed S⟩, fun S S' hS => ⟨mono S S' hS, ?_⟩, forms, ?_⟩
  · intro A hA
    obtain ⟨T, ⟨hT, b⟩, m⟩ := (memLocal S A).1 hA
    exact (memLocal S' A).2 ⟨T, ⟨hT.trans hS, b⟩, m⟩
  · intro S _
    ext A
    constructor
    · intro hA
      exact factorsThroughLinks_linksWithin (((forms S A hA.1).out 0 1).1 hA)
    · intro hA
      obtain ⟨hob, hag⟩ := isBoundedObservable_of_factorsThroughLinks hA
      exact ((forms S A hob).out 2 0).1 hag
end YangMills.Construction.InfiniteLattice.RegionObservablesProof
