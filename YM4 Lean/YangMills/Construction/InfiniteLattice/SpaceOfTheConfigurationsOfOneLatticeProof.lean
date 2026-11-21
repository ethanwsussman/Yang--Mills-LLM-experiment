import YangMills.Construction.InfiniteLattice.BondsAndTheirVariablesProof
import YangMills.Construction.InfiniteLattice.FactsFromTopologyMeasureAndFunctionTheoryProof
import YangMills.Construction.InfiniteLattice.SpaceOfTheConfigurationsOfOneLattice
import Mathlib
set_option autoImplicit false
noncomputable section
namespace YangMills.Construction.InfiniteLattice.GaugeFieldSpace
theorem countable_links (a : ℝ) : Countable (Link a) := by apply _root_.YangMills.Construction.InfiniteLattice.WilsonOperator.countable_link <;> assumption
theorem secondCountable_specialUnitary :
    SecondCountableTopology Matrices.ComplexMatrix2.specialUnitary := by apply _root_.YangMills.Construction.InfiniteLattice.WilsonOperator.secondCountable_specialUnitary <;> assumption
theorem isClosed_inverseOnOppositeFamilies (a : ℝ) : IsClosed (inverseOnOppositeFamilies a) := by apply _root_.YangMills.Construction.CutoffLinks.LinksAndTheirVariables.isClosed_setOf_opposite_eq_inv <;> assumption
theorem range_linkFamily (a : ℝ) :
    Set.range (linkFamily (a := a)) = inverseOnOppositeFamilies a := by
  ext U
  constructor
  · rintro ⟨V, rfl⟩
    exact V.2
  · intro hU
    exact ⟨⟨U, hU⟩, rfl⟩
theorem isInducing_linkFamily (a : ℝ) : Topology.IsInducing (linkFamily (a := a)) :=
  ⟨rfl⟩
theorem compactSpace_field (a : ℝ) : CompactSpace (GaugeField a) := by apply _root_.YangMills.SharedProofs.p823 <;> assumption
theorem metrizableSpace_field (a : ℝ) :
    TopologicalSpace.MetrizableSpace (GaugeField a) := by apply _root_.YangMills.Construction.InfiniteLattice.AmbientFacts.Proofs.metrizableSpace_gaugeField <;> assumption
theorem borel_gaugeField_eq_iSup (a : ℝ) :
    borel (GaugeField a) =
      ⨆ b : Link a, MeasurableSpace.comap (fun U : GaugeField a => U b)
        (borel Matrices.ComplexMatrix2.specialUnitary) := by
  have := countable_links a
  have := secondCountable_specialUnitary
  have hp : borel (Link a → Matrices.ComplexMatrix2.specialUnitary) = MeasurableSpace.pi :=
    (Pi.borelSpace (ι := Link a) (X := fun _ => Matrices.ComplexMatrix2.specialUnitary)).measurable_eq.symm
  have hc : borel (GaugeField a) =
      MeasurableSpace.comap (linkFamily (a := a))
        (borel (Link a → Matrices.ComplexMatrix2.specialUnitary)) :=
    borel_comap
  rw [hc, hp, MeasurableSpace.pi, MeasurableSpace.comap_iSup]
  refine iSup_congr fun b => ?_
  rw [MeasurableSpace.comap_comp]
  rw [BorelSpace.measurable_eq (α := Matrices.ComplexMatrix2.specialUnitary)]
  rfl
theorem topologyStatement_holds : TopologyStatement := fun a _ =>
  ⟨isClosed_inverseOnOppositeFamilies a, range_linkFamily a, isInducing_linkFamily a,
    compactSpace_field a, metrizableSpace_field a, borel_gaugeField_eq_iSup a⟩
end YangMills.Construction.InfiniteLattice.GaugeFieldSpace
