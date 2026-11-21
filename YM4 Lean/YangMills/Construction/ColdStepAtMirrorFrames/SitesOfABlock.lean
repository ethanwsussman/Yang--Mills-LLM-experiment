import YangMills.Construction.ColdChainAtEveryLevel.ChartsChainsAndShares
import Mathlib
set_option autoImplicit false
noncomputable section
open YangMills.Construction.BlockAverages
namespace YangMills.Construction
namespace ColdStepAtMirrorFrames
def SiteDecomposition : Prop :=
  ∀ F : BlockFrame, Odd F.blockSide → (∀ i, 2 ≤ F.extent i) →
    (∀ (z : F.Cell) (h : Fin 4 → ℤ), h ∈ centredCube F.blockSide →
      enclosingCell (cellCentre F.depth z + siteOfCoords F.depth h : F.Site F.depth) = z ∧
      cellOffset (cellCentre F.depth z + siteOfCoords F.depth h : F.Site F.depth) = h) ∧
    (∀ x : F.Site F.depth, cellCentre F.depth (enclosingCell x) + siteOfCoords F.depth (cellOffset x) = x ∧
      cellOffset x ∈ centredCube F.blockSide) ∧
    (∀ (x : F.Site F.depth) (i : Fin 4), IsCrossingBond (x, i) ↔
      cellOffset x i = ((F.blockSide : ℤ) - 1) / 2) ∧
    (∀ (x : F.Site F.depth) (i : Fin 4), enclosingCell (x + unitStep F.depth i) = enclosingCell x ∨
      enclosingCell (x + unitStep F.depth i) = enclosingCell x + unitStep F.top i)
end ColdStepAtMirrorFrames
end YangMills.Construction
end
