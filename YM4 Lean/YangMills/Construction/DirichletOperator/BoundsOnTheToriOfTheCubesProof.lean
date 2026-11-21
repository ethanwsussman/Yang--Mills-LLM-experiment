import YangMills.Construction.SeparatedSequences.NumbersOfThePropagatorServeOnTheToriProof
import YangMills.Construction.DirichletOperator.BoundsOnTheCoefficientsOfACubeProof
import YangMills.Construction.DirichletOperator.CornerBoundsOnTheToriOfTheCubes
import YangMills.Construction.DirichletOperator.FunctionsAndMapsOfTheCubes
import YangMills.Construction.DirichletOperator.SettingsOfASeparatedSequence
import YangMills.Construction.RegionSequence.PartitionConsequences
import YangMills.Construction.Weighted.WeightedDistBounds
import Mathlib
set_option autoImplicit false
open Set
namespace YangMills.Construction
open Dirichlet Torus RegionSequence RegionSequence.NestedRegions PartitionCubes
open DirichletGreen (fieldModulusAt)
open RegionSequence.OperatorEstimates (kernelOf avgGreenSqInv)
noncomputable section
namespace CubeTorus
section TwoLevels
variable (𝒯 : NestedRegions)
theorem nestedScale_pos (n : ℕ) : 0 < 𝒯.scale n := by apply _root_.YangMills.Construction.RegionSequence.AvgOpWeightSum.scale_pos <;> assumption
variable {𝒯} {n : ℕ}
theorem supNormAll_nonneg (f : 𝒯.FineSite → ℝ) : 0 ≤ supNormAll f := by
  refine Real.sSup_nonneg ?_
  rintro _ ⟨x, -, rfl⟩
  exact abs_nonneg _
theorem fieldSupNorm_nonneg (F : BondField 4 𝒯.side 𝒯.ξ) : 0 ≤ fieldSupNorm F :=
  Real.iSup_nonneg fun _ => supNormAll_nonneg (𝒯 := 𝒯) _
end TwoLevels
variable {𝒮 : NestedRegions} {M : ℕ}
end CubeTorus
end
end YangMills.Construction
