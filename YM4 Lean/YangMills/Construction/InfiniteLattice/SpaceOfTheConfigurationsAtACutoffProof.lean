import YangMills.Construction.InfiniteLattice.PeriodLatticesToriAndTheirWilsonMeasures
import YangMills.Construction.InfiniteLattice.SpaceOfTheConfigurationsAtACutoff
import YangMills.Construction.InfiniteLattice.WilsonKernelOnObservables
import YangMills.Construction.ReflectionPositivity.CovarianceAlgebraAndLocalisationOfTheRepresentativesProof
import Mathlib
set_option autoImplicit false
open MeasureTheory Set
noncomputable section
namespace YangMills.Construction.InfiniteLattice.FieldSpace
open YangMills.Construction.InfiniteLattice
variable {a : ℝ}
theorem continuous_eval_link (ℓ : Link a) : Continuous fun U : GaugeField a => U ℓ := by apply _root_.YangMills.Construction.ReflectionPositivity.RepresentativeCovariance.continuous_eval_link <;> assumption
theorem continuous_of_forall_link {X : Type*} [TopologicalSpace X] {f : X → GaugeField a}
    (hf : ∀ ℓ, Continuous fun x => f x ℓ) : Continuous f :=
  Continuous.subtype_mk (continuous_pi hf) fun x => (f x).2
theorem gluingIsContinuous_of_pos (ha : 0 < a) : GluingIsContinuous ha := by
  intro S hS
  classical
  refine continuous_of_forall_link fun ℓ => ?_
  by_cases hmem : ℓ ∈ S
  · have e : (fun q : LinkVariables S × GaugeField a => gluedField ha hS q.1 q.2 ℓ) =
        fun q => q.1 ⟨ℓ, hmem⟩ := funext fun q => dif_pos hmem
    rw [e]
    exact (continuous_apply _).comp continuous_fst
  · by_cases hopp : ℓ.opposite ∈ S
    · have e : (fun q : LinkVariables S × GaugeField a => gluedField ha hS q.1 q.2 ℓ) =
          fun q => (q.1 ⟨ℓ.opposite, hopp⟩)⁻¹ :=
        funext fun q => (dif_neg hmem).trans (dif_pos hopp)
      rw [e]
      exact ((continuous_apply _).comp continuous_fst).inv
    · have e : (fun q : LinkVariables S × GaugeField a => gluedField ha hS q.1 q.2 ℓ) =
          fun q => q.2 ℓ :=
        funext fun q => (dif_neg hmem).trans (dif_neg hopp)
      rw [e]
      exact (continuous_eval_link ℓ).comp continuous_snd
def positiveLinkHomeomorph (ha : 0 < a) :
    GaugeField a ≃ₜ LinkVariables (positiveLinkSet a) where
  toFun U := restrictField U (positiveLinkSet a)
  invFun V := gluedField ha subset_rfl V (trivialField a)
  left_inv U := (eq_gluedField ha subset_rfl _ (trivialField a) U (fun _ => rfl)
    (fun _ hℓ => absurd hℓ.1 hℓ.2)).symm
  right_inv V := funext fun ℓ => gluedField_apply_of_mem ha subset_rfl V _ ℓ
  continuous_toFun := continuous_pi fun ℓ => continuous_eval_link ℓ.1
  continuous_invFun := (gluingIsContinuous_of_pos ha _ subset_rfl).comp
    (continuous_id.prodMk continuous_const)
theorem secondCountable_specialUnitary :
    SecondCountableTopology Matrices.ComplexMatrix2.specialUnitary := by apply _root_.YangMills.Construction.InfiniteLattice.WilsonOperator.secondCountable_specialUnitary <;> assumption
theorem fieldsAreLinkFamilies_of_pos (ha : 0 < a) : FieldsAreLinkFamilies a := by
  have := secondCountable_specialUnitary
  have hc : CompactSpace (GaugeField a) := (positiveLinkHomeomorph ha).symm.compactSpace
  have hm : TopologicalSpace.MetrizableSpace (LinkVariables (positiveLinkSet a)) :=
    TopologicalSpace.metrizableSpace_of_t3_secondCountable _
  exact ⟨(positiveLinkHomeomorph ha).bijective, (positiveLinkHomeomorph ha).isHomeomorph, hc,
    (positiveLinkHomeomorph ha).isEmbedding.metrizableSpace⟩
theorem linkCoordinatesGenerateBorel_of_pos (ha : 0 < a) :
    LinkCoordinatesGenerateBorel a := by
  have hG := secondCountable_specialUnitary
  refine ⟨Set.to_countable _, hG, ?_⟩
  have hi : (inferInstance : TopologicalSpace (GaugeField a)) =
      TopologicalSpace.induced (positiveLinkHomeomorph ha) inferInstance :=
    (positiveLinkHomeomorph ha).isInducing.eq_induced
  have hp : borel (LinkVariables (positiveLinkSet a)) = MeasurableSpace.pi :=
    (Pi.borelSpace (ι := positiveLinkSet a)
      (X := fun _ => Matrices.ComplexMatrix2.specialUnitary)).measurable_eq.symm
  calc borel (GaugeField a)
      = @borel (GaugeField a)
          (TopologicalSpace.induced (positiveLinkHomeomorph ha) inferInstance) :=
        congrArg (@borel (GaugeField a)) hi
    _ = (borel (LinkVariables (positiveLinkSet a))).comap (positiveLinkHomeomorph ha) :=
        borel_comap
    _ = linkSigma (positiveLinkSet a) := by
        rw [hp]
        unfold MeasurableSpace.pi
        rw [MeasurableSpace.comap_iSup]
        simp only [MeasurableSpace.comap_comp]
        exact iSup_subtype (p := fun ℓ => ℓ ∈ positiveLinkSet a)
          (f := fun ℓ => MeasurableSpace.comap (fun U : GaugeField a => U ℓ.1) inferInstance)
theorem statement_holds : Statement := fun s =>
  ⟨fieldsAreLinkFamilies_of_pos (meshSize_pos s), linkCoordinatesGenerateBorel_of_pos (meshSize_pos s),
    gluingIsContinuous_of_pos (meshSize_pos s)⟩
end YangMills.Construction.InfiniteLattice.FieldSpace
