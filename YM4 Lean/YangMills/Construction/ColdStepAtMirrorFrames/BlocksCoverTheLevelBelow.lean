import YangMills.Construction.ColdStepAtMirrorFrames.MirrorTorusAndFrames
import Mathlib
set_option autoImplicit false
noncomputable section
open YangMills.Construction.BlockAverages
namespace YangMills.Construction
namespace ColdStepAtMirrorFrames
def BlocksCoverLowerLevel : Prop :=
  ∀ F : BlockFrame, Odd F.blockSide → (∀ i, 0 < F.extent i) → ∀ x : F.Site F.depth,
    x ∈ sitesOfCells (finiteCells F) F.depth
end ColdStepAtMirrorFrames
end YangMills.Construction
end
