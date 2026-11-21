import YangMills.Construction.ColdChainAtEveryLevel.LevelsAndFields
import Mathlib
set_option autoImplicit false
open YangMills.Construction.BlockAverages
namespace YangMills.Construction
namespace CellCounting
def ExpDecaySumBounded : Prop :=
  ∀ (N : ℕ) (κ : ℝ), 0 < κ → ∃ W : ℝ, 0 ≤ W ∧
    ∀ (F : BlockFrame) (ι : Type) [Fintype ι] (y : ι → F.Cell),
      (∀ z, (Finset.univ.filter fun b => y b = z).card ≤ N) →
      ∀ z : F.Cell, ∑ b, Real.exp (-(κ * (cellSupDist (y b) z : ℝ))) ≤ W
end CellCounting
end YangMills.Construction
