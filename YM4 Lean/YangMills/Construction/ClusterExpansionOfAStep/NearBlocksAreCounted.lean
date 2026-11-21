import YangMills.Construction.ClusterExpansionOfAStep.FreeClassesOfAStep
import YangMills.Construction.ClusterExpansionOfAStep.NearAClassOfASetting
import Mathlib
set_option autoImplicit false
noncomputable section
namespace YangMills.Construction.ClusterExpansionOfAStep
open TorusLumps StepSettings
def NearBlocksCardBound : Prop :=
  ∀ (L r n : ℕ) [NeZero L] [NeZero n] (θ : ClusterSupport L n),
    (blocksNear L r (clusterSupportSites L θ)).card ≤ (20 * r / L + 9) ^ 4 * supportUnitCount L r θ
end YangMills.Construction.ClusterExpansionOfAStep
end
