import YangMills.Construction.HoleBesideASecondHole.CutsLumpsBasesAndContours
import Mathlib
set_option autoImplicit false
noncomputable section
open scoped Quaternion
namespace YangMills.Construction
namespace HoleBounds
open BlockAverages LumpContours
variable {F : BlockFrame}
def IsCubicTorus (F : BlockFrame) (m : ℕ) : Prop := (∀ i, F.extent i = F.extent 0) ∧ m ≤ F.extent 0
def HasLumpWall (S : Finset F.Cell) (h : Finset (Finset (F.Site F.depth))) : Prop :=
  ∀ l ∈ h, ∀ y ∈ S, l ⊆ sitesBelow F.depth y → ∀ z ∈ torusCells F \ S, 2 < cellSupDist y z
open Classical in
def badCells (r : ℝ) (S : Finset F.Cell) (V : F.GaugeField F.top) (W Wl : F.GaugeField F.depth) :
    Finset F.Cell :=
  S.filter fun y => ∃ π : Equiv.Perm (Fin 4), ∃ b ∈ cutBonds (cutBelow F.depth S),
    (enclosingCell b.1 = y ∨ enclosingCell (b.1 + unitStep F.depth b.2) = y) ∧
      r ≤ ‖(bondCoordinate π V W b : ℍ[ℝ]) - bondCoordinate π V Wl b‖
def HoleSavingInequality {L : ℕ} (g : LumpGrid L) (a κ s cE : ℝ) (J₀ : ℕ) (S S' : Finset F.Cell)
    (hV : Finset (Finset (F.Site F.top))) (V : F.GaugeField F.top) (W : F.GaugeField F.depth)
    (b : F.Cell → F.Site F.depth) (Wl : F.GaugeField F.depth) : Prop :=
  cutEffectiveAction a F.top S' V + 8 * κ * s ^ 2 * hV.card +
      (κ / 2) * s ^ 2 * (hotLumps g s (cutBelow F.depth S) W).card +
      cE * (badCells (s / 128) S' V W Wl).card ≤
    cutEffectiveAction a F.depth
        (cutBelow F.depth S \ lumpsNeighbourhood (hotLumps g s (cutBelow F.depth S) W)) W +
      κ * s ^ 2 * (hotLumps g s (cutBelow F.depth S) W).card +
      a * ∑ c ∈ cutBonds S, contourFit J₀ (hotLumps g s (cutBelow F.depth S) W) b W V c
def cellsOffLumps (F : BlockFrame) (H : Finset (Finset (F.Site F.top))) : Finset F.Cell :=
  torusCells F \ lumpsNeighbourhood H
end HoleBounds
end YangMills.Construction
end
