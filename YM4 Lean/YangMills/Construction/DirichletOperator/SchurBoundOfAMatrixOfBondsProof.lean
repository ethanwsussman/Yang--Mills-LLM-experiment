import YangMills.Construction.RegionSequence.AvgOpWeightSum
import YangMills.Construction.RegionSequence.BlockOperatorNorms
import Mathlib
set_option autoImplicit false
open Set
noncomputable section
namespace YangMills.Construction.RegionSequence
open YangMills.Construction.Dirichlet YangMills.Construction.Torus
theorem finite_fineBond (𝒯 : NestedRegions) : Finite 𝒯.FineBond := by apply _root_.YangMills.Construction.RegionSequence.AvgOpWeightSum.finite_fineBond <;> assumption
open NestedRegions
end YangMills.Construction.RegionSequence
