import YangMills.Construction.ColdStepAtMirrorFrames.MirrorTorusAndFrames
import Mathlib
set_option autoImplicit false
noncomputable section
namespace YangMills.Construction
open BlockAverages
namespace ColdStepAtMirrorFrames
def blockDist (F : BlockFrame) (y z : F.Cell) : ℝ := cellSupDist y z
def bondBlock (F : BlockFrame) (b : ↥(chordBonds (finiteCells F))) : F.Cell := enclosingCell b.1.1
end ColdStepAtMirrorFrames
end YangMills.Construction
end
