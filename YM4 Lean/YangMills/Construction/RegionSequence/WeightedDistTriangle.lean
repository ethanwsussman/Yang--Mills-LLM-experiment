import YangMills.Construction.RegionSequence.SeparatedNestedRegions
import Mathlib
set_option autoImplicit false
namespace YangMills.Construction.RegionSequence
def WeightedDistTriangle : Prop :=
  ∀ (𝒮 : NestedRegions) (p q q' : 𝒮.Point),
    𝒮.weightedDist p q' ≤ 𝒮.weightedDist p q + 𝒮.weightedDist q q'
end YangMills.Construction.RegionSequence
