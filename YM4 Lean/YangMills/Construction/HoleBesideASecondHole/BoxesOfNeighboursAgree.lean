import YangMills.Construction.HoleBesideASecondHole.CutsLumpsBasesAndContours
import Mathlib
set_option autoImplicit false
noncomputable section
namespace YangMills.Construction.LumpContours
open YangMills.Construction.BlockAverages
variable {F : BlockFrame}
def ExcludedBoxesOfNeighboursAgree : Prop :=
  ∀ (F : BlockFrame) (g : LumpGrid F.blockSide) (J₀ : ℕ) (h : Finset (Finset (F.Site F.depth))),
    Odd F.blockSide → (∀ i, 4 ≤ F.extent i) → 4 * (11 * 2 ^ 12 * J₀) < F.blockSide →
    (∀ l ∈ h, IsLump g l) →
    (∀ y y', ¬ IsCrowded J₀ h y → ¬ IsCrowded J₀ h y' → cellSupDist y y' ≤ 1 →
      ∀ Z ∈ excludedBoxes J₀ h y,
      ((Z ∩ sitesBelow F.depth y).Nonempty ∨ (Z ∩ sitesBelow F.depth y').Nonempty) →
        Z ∈ excludedBoxes J₀ h y') ∧
    ∀ y y', ¬ IsCrowded J₀ h y → ¬ IsCrowded J₀ h y' → ∀ Z ∈ excludedBoxes J₀ h y,
      ∀ Z' ∈ excludedBoxes J₀ h y',
      (Z ∩ sitesBelow F.depth y).Nonempty → (Z' ∩ sitesBelow F.depth y').Nonempty → Z ≠ Z' →
        ¬ AreWithin 2 Z Z'
end YangMills.Construction.LumpContours
end
