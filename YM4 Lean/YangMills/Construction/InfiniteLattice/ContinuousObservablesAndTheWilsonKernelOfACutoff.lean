import YangMills.Construction.InfiniteLattice.EquivalentFormsOfTheGibbsProperty
import Mathlib
set_option autoImplicit false
open MeasureTheory Set
open YangMills.Construction.GibbsAtFixedSpacing YangMills.Construction.InfiniteLattice.GibbsEquivalences
noncomputable section
namespace YangMills.Construction.InfiniteLattice.CutoffStates
variable {a : ℝ}
theorem compactSpace_and_metrizableSpace_gaugeField (ha : 0 < a) :
    CompactSpace (GaugeField a) ∧ TopologicalSpace.MetrizableSpace (GaugeField a) := by
  have := WilsonOperator.secondCountable_specialUnitary
  have : Countable (Link a) := WilsonOperator.countable_link
  have hc : CompactSpace (GaugeField a) :=
    (WilsonOperator.gaugeFieldHomeomorph ha).symm.compactSpace
  have hs : SecondCountableTopology (GaugeField a) :=
    (WilsonOperator.gaugeFieldHomeomorph ha).secondCountableTopology
  have ht : T2Space (GaugeField a) := (WilsonOperator.gaugeFieldHomeomorph ha).symm.t2Space
  exact ⟨hc, inferInstance⟩
def IsContinuousBoundedObservable (A : GaugeField a → ℂ) : Prop :=
  IsBoundedObservable A ∧ Continuous A
theorem isContinuousBoundedObservable_iff_continuous (ha : 0 < a) (A : GaugeField a → ℂ) :
    IsContinuousBoundedObservable A ↔ Continuous A := by
  refine ⟨And.right, fun hA => ⟨?_, hA⟩⟩
  have := (compactSpace_and_metrizableSpace_gaugeField ha).1
  obtain ⟨C, hC⟩ := (isCompact_range hA).isBounded.exists_norm_le
  exact ⟨hA.measurable, C, fun U => hC _ (mem_range_self U)⟩
section Gluing
variable (ha : 0 < a) {W : Finset (Link a)}
  (hW : (W : Set (Link a)) ⊆ positiveLinkSet a) (U : GaugeField a)
  (V : W → Matrices.ComplexMatrix2.specialUnitary)
theorem glueOnLinks_apply_of_mem (b : W) : glueOnLinks ha W hW U V b = V b :=
  overwriteLinks_apply_of_mem (hasNoOppositePairs_of_subset_positiveLinks ha hW) _ U ⟨b.1, b.2⟩
theorem glueOnLinks_apply_of_not_mem {b : Link a} (hb : b ∉ W) (hr : b.opposite ∉ W) :
    glueOnLinks ha W hW U V b = U b :=
  overwriteLinks_apply_of_not_mem (hasNoOppositePairs_of_subset_positiveLinks ha hW) _ U
    (fun h => hb (Finset.mem_coe.1 h)) (fun h => hr (Finset.mem_coe.1 h))
end Gluing
theorem plaquettesTouching_eq_facesTouching (ha : 0 < a) {W : Finset (Link a)}
    (hW : (W : Set (Link a)) ⊆ positiveLinkSet a) :
    plaquettesTouching W = facesTouching W := by
  ext p
  rw [mem_plaquettesTouching_iff ha]
  constructor
  · rintro ⟨b, hb, h | h⟩
    · exact ⟨b, hb, h⟩
    · exact absurd (hW h) (opposite_notMem_positiveLinks ha
        (WilsonOperator.mem_positiveLinks_of_mem_edgeList p hb))
  · rintro ⟨b, hb, h⟩
    exact ⟨b, hb, Or.inl h⟩
theorem finite_plaquettesTouching (ha : 0 < a) {W : Finset (Link a)}
    (hW : (W : Set (Link a)) ⊆ positiveLinkSet a) :
    (plaquettesTouching W).Finite := by
  rw [plaquettesTouching_eq_facesTouching ha hW]
  exact WilsonOperator.facesTouching_finite W
theorem specKernel_eq_integral_wilsonSpecification (ha : 0 < a) (β : ℝ) {W : Finset (Link a)}
    (hW : (W : Set (Link a)) ⊆ positiveLinkSet a) (A : GaugeField a → ℂ)
    (U : GaugeField a) :
    specKernel ha β W hW A U =
      ∫ V, A (glueOnLinks ha W hW U V) ∂wilsonSpecification β W U := by
  have hs : ∀ V : W → Matrices.ComplexMatrix2.specialUnitary,
      glueOnLinks ha W hW U V = WilsonOperator.splice ha hW V U := by
    intro V
    refine WilsonOperator.eq_splice ha hW V U _ (fun b => ?_) (fun b hb => ?_)
    · exact glueOnLinks_apply_of_mem ha hW U V b
    · exact glueOnLinks_apply_of_not_mem ha hW U V (fun h => hb.2 (Finset.mem_coe.2 h))
        (fun hr => opposite_notMem_positiveLinks ha hb.1 (hW (Finset.mem_coe.2 hr)))
  have hw : ∀ U' : GaugeField a, Real.exp (-β * ∑ᶠ p ∈ plaquettesTouching W, faceEnergy U' p) =
      WilsonOperator.localWeight β W U' := fun U' => by
    unfold WilsonOperator.localWeight
    rw [plaquettesTouching_eq_facesTouching ha hW]
  have hk : specKernel ha β W hW A U =
      (∫ V : W → Matrices.ComplexMatrix2.specialUnitary,
          A (glueOnLinks ha W hW U V) *
          (Real.exp (-β * ∑ᶠ p ∈ plaquettesTouching W, faceEnergy (glueOnLinks ha W hW U V) p) : ℂ)
        ∂Matrices.ComplexMatrix2.haarPi W) /
      ((∫ V : W → Matrices.ComplexMatrix2.specialUnitary,
          Real.exp (-β * ∑ᶠ p ∈ plaquettesTouching W, faceEnergy (glueOnLinks ha W hW U V) p)
        ∂Matrices.ComplexMatrix2.haarPi W : ℝ) : ℂ) :=
    wilsonLinkKernel_apply β W _ A U
  rw [hk]
  simp only [hs, hw]
  rw [← WilsonOperator.kernelOperator_eq_integral ha hW β A U]
  unfold WilsonOperator.kernelOperator WilsonOperator.localPartition
  rw [div_eq_inv_mul]
end YangMills.Construction.InfiniteLattice.CutoffStates
