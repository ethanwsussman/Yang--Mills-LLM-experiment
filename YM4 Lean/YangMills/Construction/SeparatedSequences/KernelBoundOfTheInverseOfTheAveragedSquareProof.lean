import YangMills.Construction.SeparatedSequences.ChosenConstantsOfTheConditions
import YangMills.Construction.SeparatedSequences.OneSequenceOneSetOfObjects
import YangMills.Construction.Torus.AveragingOperatorAndMatricesProof
import Mathlib
set_option autoImplicit false
noncomputable section
namespace YangMills.Construction
open Set TorusMetric
namespace SeparatedClasses.InverseKernelBound
open SingleSequence SingleSequence.SequenceData
theorem weightedDistance_nonneg {D : Weighted.TorusData} (B : Weighted.SeparatedChain D)
    (x x' : D.Space) : 0 ≤ B.weightedDistance x x' := by apply _root_.YangMills.Construction.Weighted.AvgMatrix.weightedDistance_nonneg <;> assumption
end SeparatedClasses.InverseKernelBound
end YangMills.Construction
end
