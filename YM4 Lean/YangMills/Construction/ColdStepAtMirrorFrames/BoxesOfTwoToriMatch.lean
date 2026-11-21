import YangMills.Construction.ColdStepAtMirrorFrames.ExponentsCompareOnTwoTori
import Mathlib
set_option autoImplicit false
noncomputable section
namespace YangMills.Construction.ColdStepAtMirrorFrames
open YangMills.Construction.BlockAverages
def blockOfBond (F : BlockFrame) (b : ↥(chordBonds (finiteCells F))) : F.Cell := enclosingCell b.1.1
def NearBlocksCorrespondByOffset : Prop :=
  ∀ (F F' : BlockFrame) (Y : F.Cell) (Y' : F'.Cell) (r : ℕ), F.blockSide = F'.blockSide → F.depth = F'.depth →
    Odd F.blockSide → (∀ i, 2 * r + 2 < F.extent i) → (∀ i, 2 * r + 2 < F'.extent i) →
    ∃ (e : ↥(bondsNearCell F Y r) ≃ ↥(bondsNearCell F' Y' r))
      (φ : {z // z ∈ cellsNearCell F Y r} ≃ {z // z ∈ cellsNearCell F' Y' r}),
      BondsMatchByOffset Y Y' r e ∧ CellsMatchByOffset Y Y' r φ ∧
      (∀ k k', cellSupDist (blockOfBond F k.1) (blockOfBond F k'.1) =
        cellSupDist (blockOfBond F' (e k).1) (blockOfBond F' (e k').1)) ∧
      (∀ k, cellSupDist (blockOfBond F k.1) Y = cellSupDist (blockOfBond F' (e k).1) Y') ∧
      (∀ k z, blockOfBond F k.1 = z.1 ↔ blockOfBond F' (e k).1 = (φ z).1) ∧
      ∀ z : {z // z ∈ cellsNearCell F Y r}, z.1 = Y → (φ z).1 = Y'
end YangMills.Construction.ColdStepAtMirrorFrames
end
