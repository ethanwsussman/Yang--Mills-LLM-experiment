import YangMills.Construction.DirichletOperator.ApproximateInverseAndLocalDefects
import YangMills.Construction.DirichletOperator.DefectAsTheSumOfItsKernels
import YangMills.Construction.DirichletOperator.FactsOfALocalOperatorOfACube
import YangMills.Construction.DirichletOperator.PropagatorBoundsForDivergenceSourcesProof
import Mathlib
set_option autoImplicit false
open Set
noncomputable section
namespace YangMills.Construction.ApproxInverse
open YangMills.Construction.Dirichlet YangMills.Construction.Torus YangMills.Construction.RegionSequence YangMills.Construction.RegionSequence.NestedRegions YangMills.Construction.PartitionCubes
variable {𝒮 : NestedRegions} {M : ℕ}
theorem scale_pos (n : ℕ) : 0 < 𝒮.scale n := by apply _root_.YangMills.Construction.RegionSequence.AvgOpWeightSum.scale_pos <;> assumption
end YangMills.Construction.ApproxInverse
