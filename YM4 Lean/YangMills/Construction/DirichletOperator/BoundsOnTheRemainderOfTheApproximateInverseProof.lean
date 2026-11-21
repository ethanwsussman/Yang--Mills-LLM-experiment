import YangMills.Construction.DirichletOperator.BlockNumbersOfTheAdjointTermsProof
import YangMills.Construction.DirichletOperator.BoundsOnTheRemainderOfTheApproximateInverse
import Mathlib
set_option autoImplicit false
open YangMills.Construction.RegionSequence YangMills.Construction.RegionSequence.NestedRegions
open YangMills.Construction.RemainderEstimates
noncomputable section
namespace YangMills.Construction.ApproxInverseRemainder
variable {L : ℕ}
theorem expWeight_nonneg {S : NestedRegions} (x x' : S.Point) :
    0 ≤ RemainderEstimates.expWeight L x x' := Real.exp_nonneg _
theorem levelScale_nonneg {S : NestedRegions} (x : S.Point) : 0 ≤ S.levelScale x := by apply _root_.YangMills.Construction.RemainderAdjoint.levelScale_nonneg <;> assumption
end YangMills.Construction.ApproxInverseRemainder
