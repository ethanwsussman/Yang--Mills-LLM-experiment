import YangMills.Construction.ColdStepAtMirrorFrames.ChartEnergyInCoordinates
import YangMills.Construction.ColdStepAtMirrorFrames.KernelsOfTheBlockEnergy
import Mathlib
set_option autoImplicit false
noncomputable section
namespace YangMills.Construction
open YangMills.Construction.BlockAverages
namespace ColdStepAtMirrorFrames
def CellEnergyInCoordinates : Prop :=
  ∀ (F : BlockFrame) (a : ℝ) (Y : F.Cell) (w dw : F.Site F.depth → Fin 4 → imaginaryQuaternions)
    (V : F.GaugeField F.top)
    (dv : F.Site F.top → Fin 4 → imaginaryQuaternions), Odd F.blockSide → (∀ i, 2 ≤ F.extent i) →
    cellEnergyAlong a Y w V (chartDirections F) (chartCoordinates dw dv) =
      cellEnergyShare a Y (fun x i => w x i + dw x i) (leftTranslate dv V) ∧
    ∀ σ : Fin (chartDimension F) → ℝ,
      cellEnergyAlong a Y w V (chartDirections F) (chartCoordinates dw (fun _ _ => 0) + σ) =
        cellEnergyAlong a Y (fun x i => w x i + dw x i) V (chartDirections F) σ
end ColdStepAtMirrorFrames
end YangMills.Construction
end
