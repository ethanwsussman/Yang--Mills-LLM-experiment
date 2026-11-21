import YangMills.Construction.DirichletOperator.AdjointOfTheRemainderAsASumProof
import YangMills.Construction.DirichletOperator.PowersOfTheAdjointOfTheRemainderProof
import Mathlib
set_option autoImplicit false
noncomputable section
namespace YangMills.Construction.RemainderOperatorProof
open Set
open YangMills.Construction.Dirichlet YangMills.Construction.Torus YangMills.Construction.RegionSequence YangMills.Construction.RegionSequence.NestedRegions YangMills.Construction.PartitionCubes YangMills.Construction.Propagator YangMills.Construction.PropagatorThresholds YangMills.Construction.RemainderEstimates YangMills.Construction.Weighted
theorem finite_fineBond (hl : Torus.TorusLengthsStatement) (𝒯 : RegionSequence.NestedRegions) :
    Finite 𝒯.FineBond := by apply _root_.YangMills.Construction.RegionSequence.DifferenceAdjointsByParts.finite_fineBond <;> assumption
variable {𝒮 : RegionSequence.NestedRegions} {M : ℕ}
theorem finite_levelCube (hc : ∀ n ≤ topLevel 𝒮, (cornerSet 𝒮 M n).Finite) :
    Finite (LevelCube 𝒮 M) := by apply _root_.YangMills.Construction.RemainderAdjointSum.finite_levelCube <;> assumption
def formValues (f : (formCutSpace 𝒮).space) : 𝒮.FineBond → ℝ := f.1
end YangMills.Construction.RemainderOperatorProof
