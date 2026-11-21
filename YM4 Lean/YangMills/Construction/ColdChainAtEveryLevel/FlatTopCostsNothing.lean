import YangMills.Construction.ColdChainAtEveryLevel.ChartsChainsAndShares
import Mathlib
set_option autoImplicit false
noncomputable section
open scoped Quaternion
namespace YangMills.Construction
namespace BlockAverages
def flatField (F : BlockFrame) (j : ℕ) : F.GaugeField j := fun _ _ => 1
def flatTopVanishingStatement : Prop :=
  ∀ (F : BlockFrame) (a : ℝ) (S : Finset F.Cell), 0 ≤ a → Odd F.blockSide →
    (∀ (j : ℕ) (s : ℝ), 0 < s → IsCold S j s (flatField F j)) ∧
    (∀ j, minimalAction a S j (flatField F j) = 0) ∧
    ∀ Y, minimalCellShare a S Y (flatField F F.top) = 0
end BlockAverages
end YangMills.Construction
end
