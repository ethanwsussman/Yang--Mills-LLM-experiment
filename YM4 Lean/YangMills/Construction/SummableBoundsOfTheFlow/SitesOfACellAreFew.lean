import YangMills.Construction.ColdChainAtEveryLevel.LevelsAndFields
import Mathlib
set_option autoImplicit false
noncomputable section
open YangMills.Construction.BlockAverages
namespace YangMills.Construction
namespace CellCounting
def SitesPerCellLePow : Prop :=
  ∀ (F : BlockFrame) (S : Finset F.Cell), Odd F.blockSide → (∀ i, 2 ≤ F.extent i) → ∀ z : F.Cell,
    (Finset.univ.filter fun y : ↥(sitesOfCells S F.depth) => enclosingCell y.1 = z).card ≤ F.blockSide ^ 4
end CellCounting
end YangMills.Construction
end
