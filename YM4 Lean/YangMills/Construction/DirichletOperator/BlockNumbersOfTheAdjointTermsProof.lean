import YangMills.Construction.DirichletOperator.CornerBoundsOnTheToriOfTheCubesProof
import YangMills.Construction.DirichletOperator.AdjointDefectOfACubeThroughItsGreenOperator
import YangMills.Construction.DirichletOperator.GeometryOfCubesAndTheWeightedDistance
import YangMills.Construction.DirichletOperator.TailOfABondInACell
import YangMills.Construction.RegionSequence.CellsAndAdjoints
import Mathlib
set_option autoImplicit false
open Set
noncomputable section
namespace YangMills.Construction.RemainderAdjoint
open RegionSequence RegionSequence.NestedRegions PartitionCubes RemainderEstimates
variable {𝒮 : NestedRegions} {M : ℕ}
theorem levelScale_nonneg (y : 𝒮.Point) : 0 ≤ 𝒮.levelScale y := by
  have hL : (0 : ℝ) < 𝒮.L := by
    have := 𝒮.thirteen_le_L
    exact_mod_cast (by omega : 0 < 𝒮.L)
  have := 𝒮.ξ_pos
  unfold RegionSequence.NestedRegions.levelScale Torus.shellSpacing
  first
    | positivity
    | (unfold Torus.scaleSpacing; positivity)
theorem supBond_nonneg (f : 𝒮.FineBond → ℝ) : 0 ≤ supBond f := by apply _root_.YangMills.Construction.CornerGreen.supBond_nonneg' <;> assumption
end YangMills.Construction.RemainderAdjoint
end
