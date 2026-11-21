import YangMills.Construction.SeparatedSequences.ClassSiteFunctionsInASettingOfRegionsProof
import YangMills.Construction.SeparatedSequences.ClassSiteFunctionsInWeightedDataProof
import YangMills.Construction.SeparatedSequences.DistanceRatiosAndSumsOverTheTops
import YangMills.Construction.SeparatedSequences.OneSequenceOneSetOfObjects
import YangMills.Construction.Weighted.ChainSiteSums
import Mathlib
set_option autoImplicit false
noncomputable section
namespace YangMills.Construction
open Set PeriodicLattice PeriodicLattice.DirichletOperators TorusMetric
namespace SeparatedClasses
namespace ApexBounds
variable {C : ClassData} {Ω : ℕ → Set C.Point}
theorem one_lt_L_cast (C : ClassData) : (1 : ℝ) < (C.L : ℝ) := by
  have h := C.isAdmissible.2
  exact_mod_cast (by omega : 1 < C.L)
theorem toTorus_injective (s : SingleSequence.SequenceData) {S : ℝ} (hS : S ≠ 0) :
    Function.Injective (s.toTorus S) := by apply _root_.YangMills.Construction.SeparatedClasses.ScalarCorrespondence.toTorus_injective <;> assumption
theorem torusData_side_ne_zero (D : Weighted.TorusData) : D.side ≠ 0 := by apply _root_.YangMills.Construction.SeparatedClasses.WeightedScalarDataProof.torusData_side_ne_zero <;> assumption
end ApexBounds
end SeparatedClasses
end YangMills.Construction
end
