import YangMills.Construction.ColdChainAtEveryLevel.PairsAtOffsets
import YangMills.Construction.ColdChainAtEveryLevel.PropertiesOfTheColdChainForm
import Mathlib
set_option autoImplicit false
noncomputable section
namespace YangMills.Construction.BlockAverages
open Offsets
def sitesOfCellsAcrossFramesStatement : Prop :=
  ∀ (F F' : BlockFrame) (S : Finset F.Cell) (S' : Finset F'.Cell) (V : F.GaugeField F.top)
    (V' : F'.GaugeField F'.top) (Y : F.Cell) (Y' : F'.Cell) (r ρ j : ℕ), F'.blockSide = F.blockSide →
    F'.depth = F.depth → Odd F.blockSide → j ≤ F.top → AgreeOnBall S V S' V' Y Y' r → ρ + 2 ≤ r →
    ∀ p : Fin 4 → ℤ, WithinCellRadius F.blockSide F.top ρ j p →
      (siteAtOffset j Y p ∈ sitesOfCells S j ↔ siteAtOffset j Y' p ∈ sitesOfCells S' j)
end YangMills.Construction.BlockAverages
end
