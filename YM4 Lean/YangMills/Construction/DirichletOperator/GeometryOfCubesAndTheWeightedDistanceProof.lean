import YangMills.Construction.DirichletOperator.SeparatedSequenceOfThePropagator
import YangMills.Construction.PartitionCubes.CubeTorusTransfer
import YangMills.Construction.DirichletOperator.CubesNearALayerSite
import YangMills.Construction.DirichletOperator.DerivativeBoundsOfTheFunctionsOfACube
import YangMills.Construction.DirichletOperator.DifferenceOperatorsAgreeOnTheLocalTorus
import YangMills.Construction.DirichletOperator.GeometryOfCubesAndTheWeightedDistance
import YangMills.Construction.DirichletOperator.PositionOfTheCubesByKind
import YangMills.Construction.DirichletOperator.PositionOfTheThickenedSetsOfACube
import YangMills.Construction.DirichletOperator.SquaresOfThePartitionSumToOne
import Mathlib
set_option autoImplicit false
open Set
open scoped ENNReal
open YangMills.Construction.Dirichlet YangMills.Construction.Torus
open YangMills.Construction.RegionSequence YangMills.Construction.RegionSequence.NestedRegions
noncomputable section
namespace YangMills.Construction.PartitionCubes.CubeGeometry
theorem mollifyRadius_pos {K m M R₁ : ℕ} {𝒮 : RegionSequence.NestedRegions}
    (hs : 𝒮.IsLevelUnitChain K m M R₁) (n : ℕ) : 0 < mollifyRadius 𝒮 M n := by
  have hL : 0 < (𝒮.L : ℝ) := by
    have := 𝒮.thirteen_le_L
    exact_mod_cast (by omega : 0 < 𝒮.L)
  have hM : 0 < (M : ℝ) := by
    have h₁ := hs.separated.blockSize_isPowerGe.1
    have h₂ := 𝒮.thirteen_le_L
    exact_mod_cast (by omega : 0 < M)
  have hξ : 0 < 𝒮.scale n := mul_pos (zpow_pos hL _) 𝒮.ξ_pos
  exact div_pos (mul_pos hM hξ) (by positivity)
end YangMills.Construction.PartitionCubes.CubeGeometry
