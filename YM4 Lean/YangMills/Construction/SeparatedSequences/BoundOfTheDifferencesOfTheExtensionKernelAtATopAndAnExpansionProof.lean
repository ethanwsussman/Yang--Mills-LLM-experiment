import YangMills.Construction.Lattice.RegionCutoffSetting
import YangMills.Construction.SeparatedSequences.BasePointIsThatOfTheOperatorsAndTheFootProof
import YangMills.Construction.SeparatedSequences.ChosenConstantsOfTheConditions
import YangMills.Construction.SeparatedSequences.OneSequenceOneSetOfObjects
import YangMills.Construction.SeparatedSequences.PartitionsCubesExpansionsAndTheTriangleInequality
import YangMills.Construction.SeparatedSequences.SumsRatiosCubesThatMeetAndThePlaceOfAnExpansion
import Mathlib
set_option autoImplicit false
noncomputable section
namespace YangMills.Construction
open Set PeriodicLattice PeriodicLattice.DirichletOperators TorusMetric
namespace SeparatedClasses
namespace ExtKernelDiff
theorem L_pos (C : ClassData) : (0 : ℝ) < C.L := by apply _root_.YangMills.Construction.SeparatedClasses.AnchorAgreementProof.cast_L_pos <;> assumption
theorem one_le_L (C : ClassData) : (1 : ℝ) ≤ C.L := by
  have := C.isAdmissible.2
  exact_mod_cast (by omega : 1 ≤ C.L)
theorem coarseMesh_pos (C : ClassData) (n : ℕ) : 0 < C.toLeveledParameters.coarseMesh n :=
  zpow_pos (L_pos C) _
theorem meshSize_nonneg (C : ClassData) (j : ℤ) : 0 ≤ meshSize C.L j :=
  (zpow_pos (L_pos C) _).le
end ExtKernelDiff
end SeparatedClasses
end YangMills.Construction
end
