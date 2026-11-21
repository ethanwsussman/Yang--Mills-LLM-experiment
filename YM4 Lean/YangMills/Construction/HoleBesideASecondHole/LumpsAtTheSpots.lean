import YangMills.Construction.HoleBesideASecondHole.ComplementOfEnlargedLumpsIsRegular
import YangMills.Construction.HoleBesideASecondHole.PlacesOfAHole
import Mathlib
set_option autoImplicit false
noncomputable section
namespace YangMills.Construction
open BlockAverages LumpContours HoleBounds
namespace HoleSavings.HoleData
variable {F : BlockFrame} {L : ℕ} {g : LumpGrid L} {a s θ : ℝ} {J₀ : ℕ} (D : HoleData F g a s θ J₀)
def lumpsAtBadCells (C : ℝ) (lumpMap : F.Cell → Finset F.Cell) : Finset (Finset F.Cell) :=
  (thicken 10 (D.badCells C)).image lumpMap
def keptOffBadLumps (C : ℝ) (lumpMap : F.Cell → Finset F.Cell) : Finset F.Cell :=
  D.keptCells \ lumpsNeighbourhood (D.lumpsAtBadCells C lumpMap)
open Classical in
def IsKeptOffBadLumps (C : ℝ) (T : Finset F.Cell) : Prop :=
  (L ∣ F.extent 0 ∧ T = D.keptOffBadLumps C (lumpOf g)) ∨
    (D.cells = torusCells F ∧ IsCold D.cells F.top θ D.topField ∧
      ((2 ^ 18 ≤ F.extent 0 ∧ ∃ G : (i : Fin 4) → PeriodicLineGrid (F.extent i),
          T = D.keptOffBadLumps C fun x => gridBox G (siteCoords x)) ∨
        (F.extent 0 < 2 ^ 18 ∧ T = if (D.badCells C).Nonempty then ∅ else D.keptCells)))
end HoleSavings.HoleData
end YangMills.Construction
end
