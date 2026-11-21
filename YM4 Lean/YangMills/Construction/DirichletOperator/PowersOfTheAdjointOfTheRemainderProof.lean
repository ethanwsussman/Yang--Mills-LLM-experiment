import YangMills.Construction.DirichletOperator.TermsOfTheRemainder
import YangMills.Construction.DirichletOperator.CommutatorTermOnADecayingFormProof
import YangMills.Construction.DirichletOperator.TransferProductsOfTheRemainderProof
import Mathlib
set_option autoImplicit false
open Set
open YangMills.Construction.RegionSequence YangMills.Construction.RegionSequence.NestedRegions YangMills.Construction.PartitionCubes YangMills.Construction.Propagator YangMills.Construction.PropagatorThresholds YangMills.Construction.RemainderEstimates YangMills.Construction.Weighted YangMills.Construction.BlockCalculus YangMills.Construction.RegionSequence.CellStructure
noncomputable section
namespace YangMills.Construction.AdjointRemainderPowersProof
variable {𝒮 : NestedRegions} {M R₁ : ℕ}
theorem weightedDist_comm (y y' : 𝒮.Point) :
    𝒮.weightedDist y y' = 𝒮.weightedDist y' y := by apply _root_.YangMills.Construction.PartitionCubes.WeightedDistFromCube.weightedDist_comm <;> assumption
theorem bondInner_comm (A B : 𝒮.FineBond → ℝ) : bondInner A B = bondInner B A := by apply _root_.YangMills.Construction.RegionSequence.GradientAdjointsOnTorus.bondInner_comm <;> assumption
end YangMills.Construction.AdjointRemainderPowersProof
