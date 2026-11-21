import YangMills.Construction.HoleBesideASecondHole.LumpsAtTheSpots
import Mathlib
set_option autoImplicit false
noncomputable section
namespace YangMills.Construction.HoleSavings
def keptOffBadLumpsStatement : Prop :=
  ∀ (F : BlockAverages.BlockFrame) (L : ℕ) (g : LumpContours.LumpGrid L) (a s θ C : ℝ) (J₀ : ℕ)
    (D : HoleData F g a s θ J₀), F.blockSide = L → Odd L →
    HoleBounds.IsCubicTorus F 4096 → D.IsAdmissibleDomain →
    (∃ S₁ : Finset F.Cell, D.IsKeptOffBadLumps C S₁) ∧
    BlockAverages.IsOrthantRegular D.keptCells 1024 ∧ BlockAverages.IsCold D.keptCells F.top θ D.topField ∧
    ∀ S₁ : Finset F.Cell, D.IsKeptOffBadLumps C S₁ →
      S₁ ⊆ D.keptCells ∧ S₁ ⊆ D.coreCells C 11 ∧ BlockAverages.IsOrthantRegular S₁ 1024 ∧
      ∀ m : ℕ, (thickening D.keptCells (D.keptCells \ S₁) m).card ≤
        max ((2 ^ 17 + 2 * m) ^ 4) (2 ^ 72) * ((D.excitedCells C).card + (D.crowdedCells).card)
end YangMills.Construction.HoleSavings
end
