import YangMills.Construction.HoleBesideASecondHole.CoordinatesOfAFieldNearATop
import Mathlib
set_option autoImplicit false
noncomputable section
open scoped Quaternion
namespace YangMills.Construction.LumpContours
open YangMills.Construction.BlockAverages YangMills.Construction.HoleBounds
variable {F : BlockFrame}
def minimizerQuadraticGapStatement : Prop :=
  ∀ a : ℝ, 1 ≤ a → ∃ L₀ : ℕ, ∀ L : ℕ, Odd L → L₀ ≤ L → ∃ lam r₀ : ℝ, 0 < lam ∧ 0 < r₀ ∧
    ∀ (F : BlockFrame) (m : ℕ) (S : Finset F.Cell), F.blockSide = L → IsCubicTorus F 64 → 1024 ≤ m →
      IsOrthantRegular S m →
      ∀ (r : ℝ) (V : F.GaugeField F.top) (W Wl : F.GaugeField F.depth), 0 < r → r ≤ r₀ →
        IsCold S F.top r V → LiesNearTop r S V W → IsMinimizingField a S V Wl →
        (lam / 2) * ∑ b ∈ chordBonds S, ‖(lexBondCoordinate V W b : ℍ[ℝ]) - lexBondCoordinate V Wl b‖ ^ 2 ≤
          plainBlockEnergy a S W V - cutEffectiveAction a F.top S V
end YangMills.Construction.LumpContours
end
