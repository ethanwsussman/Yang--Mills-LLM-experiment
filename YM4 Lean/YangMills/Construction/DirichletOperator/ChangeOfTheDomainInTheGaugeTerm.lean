import YangMills.Construction.DirichletOperator.BoundsOnTheToriOfTheCubes
import Mathlib
set_option autoImplicit false
open Set
noncomputable section
namespace YangMills.Construction
open RegionSequence RegionSequence.NestedRegions PartitionCubes
namespace GaugeDomainChange
variable {𝒮 : NestedRegions} {M : ℕ}
def decayRate (L : ℕ) : ℝ := (CubeTorus.chosenConstants L).δ / (288 * (L : ℝ))
def minProduct (L : ℕ) : ℝ :=
  Weighted.separatedSumRadius 4 L (1 / 16 * (OperatorEstimates.chosenConstants L).δ)
end GaugeDomainChange
end YangMills.Construction
