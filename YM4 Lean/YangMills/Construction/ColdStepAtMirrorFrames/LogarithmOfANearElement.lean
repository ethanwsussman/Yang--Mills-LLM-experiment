import YangMills.Construction.ColdStepAtMirrorFrames.OffsetsInABlock
import Mathlib
set_option autoImplicit false
noncomputable section
open YangMills.Construction.BlockAverages
namespace YangMills.Construction.ColdStepAtMirrorFrames
open BlockOffsets
def LogNearOne : Prop :=
  ∀ g : UnitQuaternion, distFromOne g ≤ 1 →
    ∃ A : imaginaryQuaternions, expUnit A = g ∧ ‖A‖ ≤ 2 * distFromOne g
end YangMills.Construction.ColdStepAtMirrorFrames
end
