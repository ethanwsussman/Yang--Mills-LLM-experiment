import YangMills.Construction.SeparatedSequences.ClassBasePointsInASettingOfRegions
import YangMills.Construction.SeparatedSequences.ClassExpansionsInASettingOfRegionsProof
import Mathlib
set_option autoImplicit false
open Set
noncomputable section
namespace YangMills.Construction
open TorusMetric PeriodicLattice.DirichletOperators
namespace SeparatedClasses.NestedAnchors
open SingleSequence SingleSequence.SequenceData
variable (s : SequenceData) (𝒮 : RegionSequence.NestedRegions)
theorem unitTorusSide_eq : s.unitTorusSide = s.data.levelUnitTorus.toScaleData.torusSide := by apply _root_.YangMills.Construction.SeparatedClasses.NestedOneForms.unitTorusSide_eq <;> assumption
end SeparatedClasses.NestedAnchors
end YangMills.Construction
