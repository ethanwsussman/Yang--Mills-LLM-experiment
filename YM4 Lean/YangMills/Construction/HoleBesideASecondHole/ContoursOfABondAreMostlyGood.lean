import YangMills.Construction.HoleBesideASecondHole.BoxesByTheirCorners
import Mathlib
set_option autoImplicit false
noncomputable section
namespace YangMills.Construction.BondContours
open YangMills.Construction.BlockAverages YangMills.Construction.LumpContours
open Classical in
def MostContoursGoodStatement : Prop :=
  ∀ (F : BlockFrame) (J₀ Λ : ℕ) (S : Finset (Finset (F.Site F.depth))) (b : F.Cell → F.Site F.depth)
    (c : F.Cell × Fin 4),
    Odd F.blockSide → (∀ i, 64 ≤ F.extent i) → IsBaseChoice J₀ S b →
    (∀ e ∈ allContours F, ∀ x ∈ pathSites (b c.1) (contourPath b c e.1 e.2),
      x ∈ sitesBelow F.depth c.1 ∪ sitesBelow F.depth (c.1 + unitStep F.top c.2)) ∧
    (¬ IsCrowded J₀ S c.1 → ¬ IsCrowded J₀ S (c.1 + unitStep F.top c.2) →
      (∀ Z ∈ excludedBoxes J₀ S (c.1 + unitStep F.top c.2), (Z ∩ sitesBelow F.depth c.1).Nonempty →
        Z ∈ excludedBoxes J₀ S c.1) →
      (∀ Z ∈ excludedBoxes J₀ S c.1, (Z ∩ sitesBelow F.depth (c.1 + unitStep F.top c.2)).Nonempty →
        Z ∈ excludedBoxes J₀ S (c.1 + unitStep F.top c.2)) →
      ∑ Z ∈ excludedBoxes J₀ S c.1, CornerBoxes.largestSide Z ≤ Λ →
      ∑ Z ∈ excludedBoxes J₀ S (c.1 + unitStep F.top c.2), CornerBoxes.largestSide Z ≤ Λ →
      ((allContours F).filter fun e => ¬ IsGoodContour J₀ S b c e.1 e.2).card ≤
        24 * (8 * (F.blockSide * (2 * Λ) ^ 3)))
end YangMills.Construction.BondContours
end
