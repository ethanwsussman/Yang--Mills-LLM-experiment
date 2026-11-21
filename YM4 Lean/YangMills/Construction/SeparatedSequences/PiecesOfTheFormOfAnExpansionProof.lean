import YangMills.Construction.GeneralTorus.ShellsCubesAndScaledDistance
import YangMills.Construction.SeparatedSequences.ClassSiteFunctionsInASettingOfRegionsProof
import YangMills.Construction.SeparatedSequences.ChosenConstantsOfTheConditions
import YangMills.Construction.SeparatedSequences.OneSequenceOneSetOfObjects
import YangMills.Construction.SeparatedSequences.PartitionsCubesExpansionsAndTheTriangleInequality
import YangMills.Construction.Torus.ColumnsOfTheGreenOperatorOnTheTori
import YangMills.Construction.Torus.ScalarProductsTransposesAndProjectionsOfASetting
import Mathlib
set_option autoImplicit false
open Set YangMills.Construction.PeriodicLattice.DirichletOperators
noncomputable section
namespace YangMills.Construction.SeparatedClasses
namespace ExpansionFormPieces
open SingleSequence SingleSequence.SequenceData
section EvaluationMaps
variable (s : SequenceData)
theorem toTorus_injective {S : ℝ} (hS : S ≠ 0) : Function.Injective (s.toTorus S) := by apply _root_.YangMills.Construction.SeparatedClasses.ScalarCorrespondence.toTorus_injective <;> assumption
end EvaluationMaps
end ExpansionFormPieces
end YangMills.Construction.SeparatedClasses
end
