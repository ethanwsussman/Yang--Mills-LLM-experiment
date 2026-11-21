import YangMills.Construction.InfiniteLattice.ConfigurationsAreFamiliesOnTheBondsAtEverySpacing
import YangMills.Construction.InfiniteLattice.SpaceOfTheConfigurationsAtACutoffProof
import YangMills.Construction.InfiniteLattice.ThreeFormsOfTheGibbsPropertyProof
import Mathlib
set_option autoImplicit false
open MeasureTheory Set
noncomputable section
namespace YangMills.Construction.InfiniteLattice.GaugeFieldLinkFamilies
variable {a : ℝ}
theorem isPositivelyOriented_or_opposite (b : Link a) :
    b.IsPositivelyOriented ∨ b.opposite.IsPositivelyOriented := by apply _root_.YangMills.Construction.InfiniteLattice.GibbsForms.isPositivelyOriented_or_opposite <;> assumption
theorem continuous_linkValue (b : Link a) : Continuous fun U : GaugeField a => U b := by apply _root_.YangMills.Construction.ReflectionPositivity.RepresentativeCovariance.continuous_eval_link <;> assumption
theorem continuous_of_linkValues {X : Type*} [TopologicalSpace X] {f : X → GaugeField a}
    (h : ∀ b, Continuous fun x => f x b) : Continuous f := by apply _root_.YangMills.Construction.InfiniteLattice.FieldSpace.continuous_of_forall_link <;> assumption
theorem gaugeFieldOfPositive_restrictToPositive (ha : 0 < a) (U : GaugeField a) :
    gaugeFieldOfPositive ha (restrictToPositive U) = U := by
  refine Subtype.ext (funext fun b => ?_)
  change extendFromPositive (restrictToPositive U) b = U b
  unfold extendFromPositive
  by_cases h : b ∈ positiveLinks a
  · rw [dif_pos h]
    rfl
  · have h' : b.opposite ∈ positiveLinks a := (isPositivelyOriented_or_opposite b).resolve_left h
    rw [dif_neg h, dif_pos h']
    change (U b.opposite)⁻¹ = U b
    rw [U.2 b, inv_inv]
theorem restrictToPositive_gaugeFieldOfPositive (ha : 0 < a)
    (g : positiveLinks a → Matrices.ComplexMatrix2.specialUnitary) :
    restrictToPositive (gaugeFieldOfPositive ha g) = g := by
  funext b
  change extendFromPositive g b.1 = g b
  unfold extendFromPositive
  rw [dif_pos b.2]
theorem continuous_gaugeFieldOfPositive (ha : 0 < a) :
    Continuous (gaugeFieldOfPositive (a := a) ha) := by
  refine continuous_of_linkValues fun b => ?_
  change Continuous fun g : positiveLinks a → Matrices.ComplexMatrix2.specialUnitary =>
    extendFromPositive g b
  unfold extendFromPositive
  by_cases h : b ∈ positiveLinks a
  · simp only [dif_pos h]
    exact continuous_apply _
  · by_cases h' : b.opposite ∈ positiveLinks a
    · simp only [dif_neg h, dif_pos h']
      exact (continuous_apply _).inv
    · simp only [dif_neg h, dif_neg h']
      exact continuous_const
theorem continuous_glue (ha : 0 < a) (W : LinkWindow a) :
    Continuous fun q : W.Assignments × GaugeField a => W.glue ha q.1 q.2 := by
  refine continuous_of_linkValues fun b => ?_
  by_cases h : b ∈ W.links
  · have e : (fun q : W.Assignments × GaugeField a => W.glue ha q.1 q.2 b) =
        fun q => q.1 ⟨b, h⟩ := funext fun q => dif_pos h
    rw [e]
    exact (continuous_apply _).comp continuous_fst
  · by_cases h' : b.opposite ∈ W.links
    · have e : (fun q : W.Assignments × GaugeField a => W.glue ha q.1 q.2 b) =
          fun q => (q.1 ⟨b.opposite, h'⟩)⁻¹ :=
        funext fun q => (dif_neg h).trans (dif_pos h')
      rw [e]
      exact ((continuous_apply _).comp continuous_fst).inv
    · have e : (fun q : W.Assignments × GaugeField a => W.glue ha q.1 q.2 b) =
          fun q => q.2 b :=
        funext fun q => (dif_neg h).trans (dif_neg h')
      rw [e]
      exact (continuous_linkValue b).comp continuous_snd
theorem linkFamilies_holds : GaugeFieldsAreLinkFamiliesForAllSpacings := by
  intro a ha
  refine ⟨?_, ?_, continuous_glue ha⟩
  · let e : GaugeField a ≃ₜ (positiveLinks a → Matrices.ComplexMatrix2.specialUnitary) :=
      { toFun := restrictToPositive
        invFun := gaugeFieldOfPositive ha
        left_inv := gaugeFieldOfPositive_restrictToPositive ha
        right_inv := restrictToPositive_gaugeFieldOfPositive ha
        continuous_toFun := continuous_pi fun b => continuous_linkValue b.1
        continuous_invFun := continuous_gaugeFieldOfPositive ha }
    exact e.isHomeomorph
  · have hp : IsProbabilityMeasure (Matrices.ComplexMatrix2.haarPi (positiveLinks a)) := by
      unfold Matrices.ComplexMatrix2.haarPi
      infer_instance
    have : SecondCountableTopology Matrices.ComplexMatrix2 :=
      inferInstanceAs (SecondCountableTopology (Fin 2 → Fin 2 → ℂ))
    have : SecondCountableTopology Matrices.ComplexMatrix2.specialUnitary :=
      TopologicalSpace.Subtype.secondCountableTopology
        (Matrices.ComplexMatrix2.specialUnitary : Set Matrices.ComplexMatrix2)
    unfold gaugeFieldHaarMeasure
    exact Measure.isProbabilityMeasure_map
      (continuous_gaugeFieldOfPositive ha).measurable.aemeasurable
end YangMills.Construction.InfiniteLattice.GaugeFieldLinkFamilies
