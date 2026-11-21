import YangMills.Construction.HoleBesideASecondHole.BoxesByTheirCorners
import Mathlib
set_option autoImplicit false
noncomputable section
namespace YangMills.Construction.LumpContours
open BlockAverages CornerBoxes
variable {F : BlockFrame}
def lumpSeeds (h : Finset (Finset (F.Site F.depth))) (y : F.Cell) : Finset (Finset (F.Site F.depth)) :=
  (nearbyLumps h y).image lumpCollar
open Classical in
def ExcludedBoxesAtUncrowdedCell : Prop :=
  ∀ (F : BlockFrame) (g : LumpGrid F.blockSide) (J₀ : ℕ) (h : Finset (Finset (F.Site F.depth))) (y : F.Cell),
    Odd F.blockSide → (∀ i, 2 ≤ F.extent i) → 11 * 2 ^ 12 * J₀ < F.blockSide → (∀ l ∈ h, IsLump g l) →
    ¬ IsCrowded J₀ h y →
    IsLeastSeparatedCover (lumpSeeds h y) (excludedBoxes J₀ h y) ∧
      ∑ Z ∈ excludedBoxes J₀ h y, largestSide Z ≤ 11 * 2 ^ 12 * J₀ ∧
      (∀ Z ∈ excludedBoxes J₀ h y, ∃ lo hi : Fin 4 → ℤ, Z = boxSites F.depth lo hi ∧
        ∀ i, lo i ≤ hi i ∧ hi i - lo i + 1 ≤ 11 * 2 ^ 12 * J₀) ∧
      ∀ Z ∈ excludedBoxes J₀ h y, ∀ Z', IsSeparatedCover ((lumpSeeds h y).filter fun l => l ⊆ Z) Z' →
        ∃ B ∈ Z', Z ⊆ B
end YangMills.Construction.LumpContours
end
