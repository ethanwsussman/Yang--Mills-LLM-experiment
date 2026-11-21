import YangMills.Construction.HoleBesideASecondHole.PlacesOfAHole
import Mathlib
set_option autoImplicit false
noncomputable section
namespace YangMills.Construction
open BlockAverages LumpContours HoleSavings HoleBounds
namespace HoleSavings
def BadCellsBound : Prop :=
  ∀ (a κ ε Θ C CJ : ℝ) (J₀ : ℕ), 1 ≤ a → 0 < κ → 0 < ε → 1 ≤ Θ → 0 < C → 0 < CJ → 625 ≤ J₀ → ∃ L₀ : ℕ,
    ∀ L : ℕ, Odd L → L₀ ≤ L → ∀ g : LumpGrid L, ∃ s₀ : ℝ, 0 < s₀ ∧ ∀ s : ℝ, 0 < s → s ≤ s₀ →
      ∃ cE : ℝ, 0 < cE ∧ ∀ (F : BlockFrame) (D : HoleData F g a s (Θ * s) J₀) (U2 : F.FieldChain)
        (S₁ : Finset F.Cell) (Wl : F.GaugeField F.depth), F.blockSide = L → IsCubicTorus F 4096 →
        D.IsAdmissibleDomain → D.IsFillingChain C ε CJ U2 → S₁ ⊆ D.keptCells →
        IsOrthantRegular S₁ 1024 → (∀ y ∈ S₁, ∀ z ∈ D.badCells C, 10 < cellSupDist y z) →
        (∀ m : ℕ, (thickening D.keptCells (D.keptCells \ S₁) m).card ≤
          max ((2 ^ 17 + 2 * m) ^ 4) (2 ^ 72) * ((D.excitedCells C).card + (D.crowdedCells).card)) →
        IsMinimizingField a D.keptCells D.topField Wl →
        cE * (HoleBounds.badCells (s / 128) D.keptCells D.topField D.fineField Wl).card ≤
          (κ / 4) * s ^ 2 * D.hotFineLumps.card + s ^ 2 * (D.excitedCells C).card +
          (plainBlockEnergy a S₁ (U2 F.depth) D.topField - cutEffectiveAction a F.top S₁ D.topField)
end HoleSavings
end YangMills.Construction
end
