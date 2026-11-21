import YangMills.Construction.DirichletOperator.GeometryOfCubesAndTheWeightedDistance
import YangMills.Construction.DirichletOperator.RegularityOfTheLocalOperators
import Mathlib
set_option autoImplicit false
noncomputable section
namespace YangMills.Construction.ApproxInverseScales
def decayRate (L : ℕ) : ℝ := (CubeOperators.chosenConstants L).δ / (L : ℝ)
def blockLowerBound (L : ℕ) : ℝ :=
  max ((L : ℝ) ^ 5)
    (max ((L : ℝ) * (CubeTorus.chosenConstants L).minBlock)
      (6 * (L : ℝ) ^ 2 * PartitionCubes.CubeGeometry.geometryConstant))
variable {𝒮 : RegionSequence.NestedRegions}
def expWeight (y y' : 𝒮.Point) : ℝ := Real.exp (-decayRate 𝒮.L * 𝒮.weightedDist y y')
def weightedSourceSum (N : (𝒮.FineBond → ℝ) → ℝ) (y : 𝒮.Point) (f : 𝒮.FineBond → ℝ) : ℝ :=
  ∑ᶠ y'' ∈ 𝒮.allCentres, expWeight y y'' * N (RegionSequence.NestedRegions.cellCutBond y'' f)
def outerCube (y : 𝒮.Point) : Set 𝒮.Point :=
  RegionSequence.NestedRegions.cubeHalfSide y (2 * 𝒮.levelScale y)
end YangMills.Construction.ApproxInverseScales
