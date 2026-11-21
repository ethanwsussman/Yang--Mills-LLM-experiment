import YangMills.Construction.HoleBesideASecondHole.TheInequalityOfAHole
import Mathlib
set_option autoImplicit false
noncomputable section
open scoped Quaternion
namespace YangMills.Construction
namespace HoleBounds
open BlockAverages LumpContours
variable {F : BlockFrame}
def wallMargin : ℕ := 5
def CellsSeparated (m : ℕ) (X Y : Finset F.Cell) : Prop := ∀ x ∈ X, ∀ y ∈ Y, m ≤ cellSupDist x y
def AgreesWithMinimizerNear (X S : Finset F.Cell) (W Wl : F.GaugeField F.depth) : Prop :=
  ∀ e ∈ cutBonds (cutBelow F.depth S), ∀ z ∈ X, cellSupDist (enclosingCell e.1) z ≤ wallMargin →
    W e.1 e.2 = Wl e.1 e.2
open Classical in
def chartDeviantCells (r : ℝ) (S : Finset F.Cell) (V : F.GaugeField F.top) (W Wl : F.GaugeField F.depth) :
    Finset F.Cell :=
  S.filter fun y => ∃ e ∈ cutBonds (cutBelow F.depth S), enclosingCell e.1 = y ∧
    r ≤ ‖(bondCoordinate 1 V W e : ℍ[ℝ]) - bondCoordinate 1 V Wl e‖
def HoleSavingWorkingForm {L : ℕ} (g : LumpGrid L) (a κ s cE : ℝ) (J₀ : ℕ) (S₀ S : Finset F.Cell)
    (hV : Finset (Finset (F.Site F.top))) (V : F.GaugeField F.top) (W : F.GaugeField F.depth)
    (b : F.Cell → F.Site F.depth) (Wl : F.GaugeField F.depth) : Prop :=
  cutEffectiveAction a F.top S V + 6 * κ * s ^ 2 * hV.card +
      (κ / 4) * s ^ 2 * (hotLumps g s (cutBelow F.depth S₀) W).card +
      cE * (chartDeviantCells (s / 128) S V W Wl).card ≤
    cutEffectiveAction a F.depth
        (cutBelow F.depth S₀ \ lumpsNeighbourhood (hotLumps g s (cutBelow F.depth S₀) W)) W +
      κ * s ^ 2 * (hotLumps g s (cutBelow F.depth S₀) W).card +
      a * ∑ c ∈ cutBonds S₀, contourFit J₀ (hotLumps g s (cutBelow F.depth S₀) W) b W V c
structure HoleSavingWorkingBounds {L : ℕ} (g : LumpGrid L) (a κ s cE : ℝ) (J₀ : ℕ) : Prop where
  holed : ∀ F : BlockFrame, F.blockSide = L → IsCubicTorus F 4096 → L ∣ F.extent 0 →
    ∀ (H : Finset (Finset (F.Site F.top))), (∀ l ∈ H, IsLump g l) →
    ∀ (V : F.GaugeField F.top) (W : F.GaugeField F.depth) (b : F.Cell → F.Site F.depth)
      (Wl : F.GaugeField F.depth),
      CellsSeparated (2 * wallMargin) (lumpsNeighbourhood (hotLumps g s (cellsOffLumps F H) V))
        (lumpsNeighbourhood H) →
      IsMinimizingField a (cellsOffLumps F H \ lumpsNeighbourhood (hotLumps g s (cellsOffLumps F H) V)) V Wl →
      AgreesWithMinimizerNear (lumpsNeighbourhood H)
        (cellsOffLumps F H \ lumpsNeighbourhood (hotLumps g s (cellsOffLumps F H) V)) W Wl →
      IsBaseChoice J₀ (hotLumps g s (cutBelow F.depth (cellsOffLumps F H)) W) b →
      HoleSavingWorkingForm g a κ s cE J₀ (cellsOffLumps F H)
        (cellsOffLumps F H \ lumpsNeighbourhood (hotLumps g s (cellsOffLumps F H) V))
        (hotLumps g s (cellsOffLumps F H) V) V W b Wl
  cold : ∀ F : BlockFrame, F.blockSide = L → IsCubicTorus F 4096 →
    ∀ (V : F.GaugeField F.top) (W : F.GaugeField F.depth) (b : F.Cell → F.Site F.depth)
      (Wl : F.GaugeField F.depth),
      IsCold (torusCells F) F.top (9 / 8 * s) V →
      IsMinimizingField a (torusCells F) V Wl →
      IsBaseChoice J₀ (hotLumps g s (cutBelow F.depth (torusCells F)) W) b →
      HoleSavingWorkingForm g a κ s cE J₀ (torusCells F) (torusCells F) ∅ V W b Wl
end HoleBounds
end YangMills.Construction
end
