import YangMills.Construction.DirichletOperator.SeparatedSequenceOfThePropagator
import YangMills.Construction.PartitionCubes.LocalOperators
import YangMills.Construction.RegionSequence.DifferenceAdjointsByParts
import Mathlib
set_option autoImplicit false
open Set
open YangMills.Construction.Dirichlet YangMills.Construction.Torus
open YangMills.Construction.RegionSequence YangMills.Construction.RegionSequence.NestedRegions
noncomputable section
namespace YangMills.Construction.PartitionCubes.TransferAdjointness
variable {𝒮 : RegionSequence.NestedRegions} {M : ℕ}
theorem finite_fineSite (hl : Torus.TorusLengthsStatement) (𝒯 : RegionSequence.NestedRegions) :
    Finite 𝒯.FineSite := by apply _root_.YangMills.Construction.RegionSequence.DifferenceAdjointsByParts.finite_fineSite <;> assumption
theorem finite_fineBond (hl : Torus.TorusLengthsStatement) (𝒯 : RegionSequence.NestedRegions) :
    Finite 𝒯.FineBond := by apply _root_.YangMills.Construction.RegionSequence.DifferenceAdjointsByParts.finite_fineBond <;> assumption
end YangMills.Construction.PartitionCubes.TransferAdjointness
