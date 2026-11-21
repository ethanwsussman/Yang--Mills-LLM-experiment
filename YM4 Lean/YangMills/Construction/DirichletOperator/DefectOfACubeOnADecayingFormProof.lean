import YangMills.Construction.DirichletOperator.BoundsOfTheBracketOnALocalTorusProof
import YangMills.Construction.DirichletOperator.BlockNumbersOfTheAdjointTermsProof
import YangMills.Construction.DirichletOperator.ChangeOfTheLongitudinalOperatorInNorm
import YangMills.Construction.DirichletOperator.FormDecayingFromAPointOfACube
import YangMills.Construction.DirichletOperator.CommutatorOfTheLongitudinalOperatorOfACube
import YangMills.Construction.DirichletOperator.PropagatorBoundsForSourcesInFormsProof
import Mathlib
set_option autoImplicit false
open Set
noncomputable section
namespace YangMills.Construction
open YangMills.Construction.Torus YangMills.Construction.RegionSequence YangMills.Construction.RegionSequence.NestedRegions YangMills.Construction.PartitionCubes
namespace CubeDefect
variable {𝒩 : NestedRegions} {M : ℕ}
theorem finite_fineBond (hlen : TorusLengthsStatement) (𝒯 : NestedRegions) : Finite 𝒯.FineBond := by apply _root_.YangMills.Construction.RegionSequence.DifferenceAdjointsByParts.finite_fineBond <;> assumption
section Norms
variable {𝒯 : NestedRegions} [Fintype 𝒯.FineBond]
end Norms
end CubeDefect
end YangMills.Construction
