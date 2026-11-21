import YangMills.Construction.ColdStepAtMirrorFrames.MirrorTorusAndFrames
import Mathlib
set_option autoImplicit false
noncomputable section
namespace YangMills.Construction
open BlockAverages ColdStepAtMirrorFrames
namespace Estimates
def cellBondsCardStatement : Prop :=
  ∀ (F : BlockFrame), Odd F.blockSide → (∀ i, 2 ≤ F.extent i) → ∀ z : F.Cell,
    (Finset.univ.filter fun b : ↥(chordBonds (finiteCells F)) => enclosingCell b.1.1 = z).card ≤
      4 * F.blockSide ^ 4
end Estimates
end YangMills.Construction
end
