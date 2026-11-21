import YangMills.Construction.DirichletOperator.BoundsOnTheRemainderOfTheApproximateInverse
import YangMills.Construction.DirichletOperator.ScalesOfTheApproximateInverse
import YangMills.Construction.DirichletOperator.ExpansionTerms
import Mathlib
set_option autoImplicit false
noncomputable section
namespace YangMills.Construction
open Set
open RegionSequence RegionSequence.NestedRegions PartitionCubes Propagator Weighted
namespace PropagatorThresholds
def mainRate (L : ℕ) : ℝ := RemainderEstimates.remainderRate L / 2
def minBlock (L : ℕ) : ℝ :=
  max (ApproxInverseScales.blockLowerBound L)
    (max (RegionSequence.OperatorEstimates.chosenConstants L).minBlock
      (max (ApproxInverseRemainder.chosenConstants L).minBlock
        (2 * |(ApproxInverseRemainder.chosenConstants L).C| *
          separatedSumConst 4 L (RemainderEstimates.remainderRate L / 2))))
def minGapBlock (L : ℕ) : ℝ :=
  max (RegionSequence.OperatorEstimates.chosenConstants L).minProduct
    (max (ApproxInverseRemainder.chosenConstants L).minProduct
      (separatedSumRadius 4 L (RemainderEstimates.remainderRate L / 8)))
structure IsAboveThresholds (𝒮 : NestedRegions) (K m M R₁ : ℕ) : Prop where
  unitSeparated : IsUnitSeparated 𝒮 K m M R₁
  minBlock_le : minBlock 𝒮.L ≤ (M : ℝ)
  minGapBlock_le : minGapBlock 𝒮.L ≤ (R₁ : ℝ) * (M : ℝ)
end PropagatorThresholds
end YangMills.Construction
