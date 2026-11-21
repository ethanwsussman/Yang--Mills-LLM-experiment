import YangMills.Construction.ClusterExpansionOfAStep.LumpsOnATorus
import Mathlib
set_option autoImplicit false
noncomputable section
namespace YangMills.Construction.TorusLumps
open YangMills.Construction.TorusFields
def FineDistanceLeBlockDistance : Prop :=
  ∀ (n L : ℕ) [NeZero n] [NeZero L] (x x' : TorusSite (n * L)),
    supDist x x' ≤ L * supDist (parentBlock L x) (parentBlock L x') + L
end YangMills.Construction.TorusLumps
end
