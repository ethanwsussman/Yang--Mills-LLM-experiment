import YangMills.Construction.ClusterExpansionOfAStep.AttachedClustersOfAStep
import YangMills.Construction.ClusterExpansionOfAStep.OffsetsAboveABox
import Mathlib
set_option autoImplicit false
set_option linter.unusedSectionVars false
set_option linter.unusedVariables false
noncomputable section
namespace YangMills.Construction.CongruentStates
variable {R : StepSettings.StepSetup} {n n' : ℕ} [NeZero n] [NeZero n'] {y : TorusFields.TorusSite n}
  {y' : TorusFields.TorusSite n'} {m : ℕ}
structure RecordsAgree (p : StepSettings.CoarseState R n) (p' : StepSettings.CoarseState R n')
    (y : TorusFields.TorusSite n) (y' : TorusFields.TorusSite n') (m : ℕ) : Prop where
  markAt_eq : ∀ a, TorusFields.OffsetInBox m a →
    p.markAt (y + TorusFields.siteOfInt a) = p'.markAt (y' + TorusFields.siteOfInt a)
  support_left : ∀ z, (p.markAt z).isSome → ∃ a, TorusFields.OffsetInBox m a ∧ z = y + TorusFields.siteOfInt a
  support_right : ∀ z, (p'.markAt z).isSome → ∃ a, TorusFields.OffsetInBox m a ∧ z = y' + TorusFields.siteOfInt a
variable {p : StepSettings.CoarseState R n} {p' : StepSettings.CoarseState R n'}
theorem RecordsAgree.symm (hagree : RecordsAgree p p' y y' m) : RecordsAgree p' p y' y m :=
  ⟨fun a ha => (hagree.markAt_eq a ha).symm, hagree.support_right, hagree.support_left⟩
theorem RecordsAgree.markedZone_congruent (hagree : RecordsAgree p p' y y' m) :
    TorusLumps.CongruentInBoxes p.markedZone p'.markedZone y y' m := by
  refine ⟨fun z hz => hagree.support_left z (ClusterExpansionOfAStep.mem_controlRegion.mp hz),
    fun z hz => hagree.support_right z (ClusterExpansionOfAStep.mem_controlRegion.mp hz), fun a ha => ?_⟩
  rw [ClusterExpansionOfAStep.mem_controlRegion, ClusterExpansionOfAStep.mem_controlRegion, hagree.markAt_eq a ha]
abbrev refinedCentre (R : StepSettings.StepSetup) (y : TorusFields.TorusSite n) :
    TorusFields.TorusSite (n * R.params.side) :=
  CongruentBoxes.blockCentre R.params.side y
abbrev refinedBox (R : StepSettings.StepSetup) (m : ℕ) : ℕ := CongruentBoxes.refinedRadius R.params.side m
section Refined
variable (hL : Odd R.params.side)
include hL
theorem RecordsAgree.markAt_parentBlock (hagree : RecordsAgree p p' y y' m) {h : Fin 4 → ℤ}
    (hh : TorusFields.OffsetInBox (refinedBox R m) h) :
    p.markAt (TorusLumps.parentBlock R.params.side (refinedCentre R y + TorusFields.siteOfInt h)) =
      p'.markAt (TorusLumps.parentBlock R.params.side (refinedCentre R y' + TorusFields.siteOfInt h)) := by
  rw [CongruentBoxes.parentBlock_blockCentre_add, CongruentBoxes.parentBlock_blockCentre_add]
  exact hagree.markAt_eq _ ((CongruentBoxes.offsetInBox_refinedRadius_iff hL).mp hh)
theorem RecordsAgree.storedField_eq (hagree : RecordsAgree p p' y y' m) {h : Fin 4 → ℤ}
    (hh : TorusFields.OffsetInBox (refinedBox R m) h) (i : Fin 4) :
    p.storedField (refinedCentre R y + TorusFields.siteOfInt h) i =
      p'.storedField (refinedCentre R y' + TorusFields.siteOfInt h) i := by
  simp only [StepSettings.CoarseState.storedField, StepSettings.CoarseState.fieldWithStoredLinks,
    hagree.markAt_parentBlock hL hh, CongruentBoxes.siteOffset_blockCentre_add, TorusFields.trivialField]
theorem RecordsAgree.labelAt_eq (hagree : RecordsAgree p p' y y' m) {h : Fin 4 → ℤ}
    (hh : TorusFields.OffsetInBox (refinedBox R m) h) :
    p.labelAt (refinedCentre R y + TorusFields.siteOfInt h) =
      p'.labelAt (refinedCentre R y' + TorusFields.siteOfInt h) := by
  simp only [StepSettings.CoarseState.labelAt, hagree.markAt_parentBlock hL hh,
    CongruentBoxes.siteOffset_blockCentre_add]
theorem RecordsAgree.exists_offset_of_isSome (hagree : RecordsAgree p p' y y' m)
    {x : TorusFields.TorusSite (n * R.params.side)}
    (hx : (p.markAt (TorusLumps.parentBlock R.params.side x)).isSome) :
    ∃ h, TorusFields.OffsetInBox (refinedBox R m) h ∧ x = refinedCentre R y + TorusFields.siteOfInt h := by
  obtain ⟨a, ha, he⟩ := hagree.support_left _ hx
  exact ⟨_, CongruentBoxes.offsetInBox_refinedOffset hL ha _, CongruentBoxes.eq_blockCentre_add_of_parentBlock he⟩
theorem isSome_of_labelAt_ne {q : StepSettings.CoarseState R n} {z : TorusFields.TorusSite (n * R.params.side)}
    (h : q.labelAt z ≠ Sum.inl ()) : (q.markAt (TorusLumps.parentBlock R.params.side z)).isSome := by
  by_contra hc
  apply h
  simp only [Option.not_isSome_iff_eq_none] at hc
  simp [StepSettings.CoarseState.labelAt, hc]
theorem RecordsAgree.labelSet_congruent (hagree : RecordsAgree p p' y y' m) :
    TorusLumps.CongruentInBoxes p.labelSet p'.labelSet (refinedCentre R y) (refinedCentre R y') (refinedBox R m) := by
  refine ⟨fun z hz => ?_, fun z hz => ?_, fun h hh => ?_⟩
  · exact hagree.exists_offset_of_isSome hL (isSome_of_labelAt_ne hL (ClusterExpansionOfAStep.mem_labelSet.mp hz))
  · exact hagree.symm.exists_offset_of_isSome hL (isSome_of_labelAt_ne hL (ClusterExpansionOfAStep.mem_labelSet.mp hz))
  · rw [ClusterExpansionOfAStep.mem_labelSet, ClusterExpansionOfAStep.mem_labelSet, hagree.labelAt_eq hL hh]
theorem RecordsAgree.labeling_eq (hagree : RecordsAgree p p' y y' m) {h : Fin 4 → ℤ}
    (hh : TorusFields.OffsetInBox (refinedBox R m) h)
    (hz : refinedCentre R y + TorusFields.siteOfInt h ∈ p.labelSet)
    (hz' : refinedCentre R y' + TorusFields.siteOfInt h ∈ p'.labelSet) :
    p.labeling ⟨_, hz⟩ = p'.labeling ⟨_, hz'⟩ := by
  have e1 := ClusterExpansionOfAStep.labelAt_eq_inr_labeling p ⟨_, hz⟩
  have e2 := ClusterExpansionOfAStep.labelAt_eq_inr_labeling p' ⟨_, hz'⟩
  have e3 := hagree.labelAt_eq hL hh
  simp only at e1 e2
  rw [e1, e2] at e3
  exact Sum.inr.inj e3
theorem RecordsAgree.mem_storedBadBonds_iff (hagree : RecordsAgree p p' y y' m) {h : Fin 4 → ℤ}
    (hh : TorusFields.OffsetInBox (refinedBox R m) h) (i : Fin 4) :
    ((refinedCentre R y + TorusFields.siteOfInt h, i) : TorusFields.TorusBond _) ∈ p.storedBadBonds ↔
      ((refinedCentre R y' + TorusFields.siteOfInt h, i) : TorusFields.TorusBond _) ∈ p'.storedBadBonds := by
  rw [ClusterExpansionOfAStep.mem_storedBadBonds, ClusterExpansionOfAStep.mem_storedBadBonds]
  simp only [hagree.markAt_parentBlock hL hh, CongruentBoxes.siteOffset_blockCentre_add]
theorem RecordsAgree.mem_storedFieldBonds_iff (hagree : RecordsAgree p p' y y' m) {h : Fin 4 → ℤ}
    (hh : TorusFields.OffsetInBox (refinedBox R m) h) (i : Fin 4) :
    ((refinedCentre R y + TorusFields.siteOfInt h, i) : TorusFields.TorusBond _) ∈ p.storedFieldBonds ↔
      ((refinedCentre R y' + TorusFields.siteOfInt h, i) : TorusFields.TorusBond _) ∈ p'.storedFieldBonds := by
  rw [ClusterExpansionOfAStep.mem_storedFieldBonds, ClusterExpansionOfAStep.mem_storedFieldBonds]
  simp only [hagree.markAt_parentBlock hL hh, CongruentBoxes.siteOffset_blockCentre_add]
theorem isSome_of_mem_storedBadBonds {q : StepSettings.CoarseState R n}
    {c : TorusFields.TorusBond (n * R.params.side)} (h : c ∈ q.storedBadBonds) :
    (q.markAt (TorusLumps.parentBlock R.params.side c.1)).isSome := by
  obtain ⟨s, hs, -⟩ := ClusterExpansionOfAStep.mem_storedBadBonds.mp h
  simp [hs]
theorem isSome_of_mem_storedFieldBonds {q : StepSettings.CoarseState R n}
    {c : TorusFields.TorusBond (n * R.params.side)} (h : c ∈ q.storedFieldBonds) :
    (q.markAt (TorusLumps.parentBlock R.params.side c.1)).isSome := by
  obtain ⟨s, hs, -⟩ := ClusterExpansionOfAStep.mem_storedFieldBonds.mp h
  simp [hs]
theorem RecordsAgree.badSites_congruent (hagree : RecordsAgree p p' y y' m) :
    TorusLumps.CongruentInBoxes (p.storedBadBonds.image Prod.fst) (p'.storedBadBonds.image Prod.fst)
      (refinedCentre R y) (refinedCentre R y') (refinedBox R m) := by
  refine ⟨fun z hz => ?_, fun z hz => ?_, fun h hh => ?_⟩
  · obtain ⟨c, hc, rfl⟩ := Finset.mem_image.mp hz
    exact hagree.exists_offset_of_isSome hL (isSome_of_mem_storedBadBonds hL hc)
  · obtain ⟨c, hc, rfl⟩ := Finset.mem_image.mp hz
    exact hagree.symm.exists_offset_of_isSome hL (isSome_of_mem_storedBadBonds hL hc)
  · constructor
    · intro hz
      obtain ⟨c, hc, he⟩ := Finset.mem_image.mp hz
      obtain ⟨x, i⟩ := c
      simp only at he
      subst he
      exact Finset.mem_image.mpr ⟨_, (hagree.mem_storedBadBonds_iff hL hh i).mp hc, rfl⟩
    · intro hz
      obtain ⟨c, hc, he⟩ := Finset.mem_image.mp hz
      obtain ⟨x, i⟩ := c
      simp only at he
      subst he
      exact Finset.mem_image.mpr ⟨_, (hagree.mem_storedBadBonds_iff hL hh i).mpr hc, rfl⟩
end Refined
end YangMills.Construction.CongruentStates
end
