import YangMills.Construction.HoleBesideASecondHole.PlacesOfAHole
import Mathlib
set_option autoImplicit false
noncomputable section
namespace YangMills.Construction.HoleSavings
open YangMills.Construction.BlockAverages YangMills.Construction.LumpContours
open YangMills.Construction.HoleBounds
def excitedCellsPayStatement : Prop :=
  ∀ (F : BlockFrame) (L : ℕ) (g : LumpGrid L) (a s θ C : ℝ) (J₀ : ℕ) (D : HoleData F g a s θ J₀)
    (S₁ : Finset F.Cell), 0 ≤ a → F.blockSide = L → Odd L → IsCubicTorus F 4096 → S₁ ⊆ D.cells →
    (∀ y ∈ S₁, ∀ z ∈ D.badCells C, 10 < cellSupDist y z) →
    C * s ^ 2 * (D.excitedCells C).card ≤ 10 ^ 4 * (D.totalEnergy - D.energyOn S₁)
end YangMills.Construction.HoleSavings
end
