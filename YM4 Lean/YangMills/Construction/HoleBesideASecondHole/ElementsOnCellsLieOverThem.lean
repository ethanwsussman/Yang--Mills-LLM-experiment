import YangMills.Construction.HoleBesideASecondHole.PlacesOfAHole
import Mathlib
set_option autoImplicit false
noncomputable section
namespace YangMills.Construction.HoleSavings
open YangMills.Construction.BlockAverages YangMills.Construction.LumpContours
def energyOnLeEnergyOverStatement : Prop :=
  ∀ (F : BlockFrame) (L : ℕ) (g : LumpGrid L) (a s θ : ℝ) (J₀ : ℕ) (D : HoleData F g a s θ J₀),
    0 ≤ a → Odd F.blockSide → (∀ i, 0 < F.extent i) →
    (∀ X B : Finset F.Cell, X ⊆ D.cells → X ⊆ B → D.energyOn X ≤ D.energyOver B) ∧
    ∀ (B : Finset F.Cell) (c : F.Cell × Fin 4), c ∈ cutBonds D.cells →
      (c.1 ∈ B ∨ c.1 + unitStep F.top c.2 ∈ B) →
      a * D.topBondFit c ≤ D.energyOver B
end YangMills.Construction.HoleSavings
end
