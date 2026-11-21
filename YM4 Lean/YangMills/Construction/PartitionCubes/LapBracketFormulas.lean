import YangMills.Construction.PartitionCubes.LocalOperators
import Mathlib
set_option autoImplicit false
open Set
noncomputable section
namespace YangMills.Construction.PartitionCubes
open RegionSequence.NestedRegions
variable {𝒯 : RegionSequence.NestedRegions}
def onSites (φ : 𝒯.Point → ℝ) : 𝒯.FineSite → ℝ := fun x => φ (x : 𝒯.Point)
end YangMills.Construction.PartitionCubes
