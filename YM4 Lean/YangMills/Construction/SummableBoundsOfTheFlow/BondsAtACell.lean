import YangMills.Construction.ColdChainAtEveryLevel.LevelsAndFields
import Mathlib
set_option autoImplicit false
open YangMills.Construction.BlockAverages
namespace YangMills.Construction.CellCounting
def BondsPerCellBounded : Prop :=
  ∀ L : ℕ, 0 < L → ∃ N : ℕ, ∀ F : BlockFrame, F.blockSide = L → ∀ (ι : Type) [Fintype ι]
    (j : ι → F.Site F.depth × Fin 4), Function.Injective j → ∀ z : F.Cell,
      (Finset.univ.filter fun b => enclosingCell (j b).1 = z).card ≤ N
end YangMills.Construction.CellCounting
