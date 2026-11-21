import YangMills.Construction.InfiniteLattice.FactsOfTheBondsConfigurationsAndMotionsAtOneSpacing
import Mathlib
set_option autoImplicit false
noncomputable section
namespace YangMills.Construction.InfiniteLattice.FieldSpace
open InfiniteLattice
def FieldsAreLinkFamilies (a : ℝ) : Prop :=
  Function.Bijective (fun U : GaugeField a => restrictField U (positiveLinkSet a)) ∧
    IsHomeomorph (fun U : GaugeField a => restrictField U (positiveLinkSet a)) ∧
    CompactSpace (GaugeField a) ∧ TopologicalSpace.MetrizableSpace (GaugeField a)
def LinkCoordinatesGenerateBorel (a : ℝ) : Prop :=
  (positiveLinkSet a).Countable ∧
    SecondCountableTopology Matrices.ComplexMatrix2.specialUnitary ∧
    borel (GaugeField a) = linkSigma (positiveLinkSet a)
def GluingIsContinuous {a : ℝ} (ha : 0 < a) : Prop :=
  ∀ (S : Set (Link a)) (hS : S ⊆ positiveLinkSet a),
    Continuous fun q : LinkVariables S × GaugeField a => gluedField ha hS q.1 q.2
theorem meshSize_pos (p : Conventions.StandingParameters) :
    0 < PeriodicLattice.meshSize p.L ((p.K : ℕ) : ℤ) := by apply _root_.YangMills.Construction.InfiniteLattice.OneSpacing.meshSize_pos <;> assumption
def Statement : Prop :=
  ∀ p : Conventions.StandingParameters,
    FieldsAreLinkFamilies (PeriodicLattice.meshSize p.L ((p.K : ℕ) : ℤ)) ∧
    LinkCoordinatesGenerateBorel (PeriodicLattice.meshSize p.L ((p.K : ℕ) : ℤ)) ∧
    GluingIsContinuous (meshSize_pos p)
end YangMills.Construction.InfiniteLattice.FieldSpace
end
