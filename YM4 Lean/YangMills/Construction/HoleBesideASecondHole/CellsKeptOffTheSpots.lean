import YangMills.Construction.HoleBesideASecondHole.PlacesOfAHole
import Mathlib
set_option autoImplicit false
noncomputable section
namespace YangMills.Construction
open BlockAverages LumpContours HoleSavings HoleBounds
namespace HoleSavings
def KeptCellsAwayFromBad : Prop :=
  ∀ (F : BlockFrame) (L : ℕ) (g : LumpGrid L) (a s θ C : ℝ) (J₀ : ℕ) (D : HoleData F g a s θ J₀),
    F.blockSide = L → Odd L → IsCubicTorus F 4096 → D.IsAdmissibleDomain →
    IsOrthantRegular D.keptCells 1024 ∧ IsCold D.keptCells F.top θ D.topField ∧
    ∃ S₁ : Finset F.Cell, S₁ ⊆ D.keptCells ∧ IsOrthantRegular S₁ 1024 ∧
      (∀ y ∈ S₁, ∀ z ∈ D.badCells C, 10 < cellSupDist y z) ∧
      ∀ m : ℕ, (thickening D.keptCells (D.keptCells \ S₁) m).card ≤
        max ((2 ^ 17 + 2 * m) ^ 4) (2 ^ 72) * ((D.excitedCells C).card + (D.crowdedCells).card)
end HoleSavings
end YangMills.Construction
end
