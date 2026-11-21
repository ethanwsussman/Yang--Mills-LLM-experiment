import YangMills.Construction.CellOfTheFlow.WindowsOfACell
import Mathlib
set_option autoImplicit false
noncomputable section
namespace YangMills.Construction.CellWindows
open YangMills.Construction.TorusLumps
def cellBlocksEqRefinedCellStatement : Prop :=
  ∀ (L : ℕ) [NeZero L] (G : CellGrid) (n : ℕ) [NeZero n] (κ : Fin 4 → ℤ),
    sitesInBlocks L (G.cell n κ) = (G.refine L).cell (n * L) κ
end YangMills.Construction.CellWindows
end
