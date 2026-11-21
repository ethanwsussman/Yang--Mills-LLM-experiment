import YangMills.Construction.SummableBoundsOfTheFlow.NearPairingOfTheBox
import Mathlib
set_option autoImplicit false
noncomputable section
namespace YangMills.Construction.TorusComparison
open BlockAverages ColdStepAtMirrorFrames
def bondsNearCellsPairStatement : Prop :=
  ∀ (F F' : BlockFrame) (Y : F.Cell) (Y' : F'.Cell) (q : ℕ), Odd F.blockSide → F'.blockSide = F.blockSide →
    (∀ i, 2 * q + 2 < F.extent i) → (∀ i, 2 * q + 2 < F'.extent i) →
    ∃ (ι : Type) (_ : Fintype ι) (_ : DecidableEq ι) (j : ι → ↥(chordBonds (finiteCells F)))
      (j' : ι → ↥(chordBonds (finiteCells F'))), IsShortPairing Y Y' q j j'
end YangMills.Construction.TorusComparison
end
