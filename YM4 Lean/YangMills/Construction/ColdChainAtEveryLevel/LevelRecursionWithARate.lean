import YangMills.Construction.ColdChainAtEveryLevel.LevelRecursionNearACell
import Mathlib
set_option autoImplicit false
noncomputable section
open scoped Quaternion
namespace YangMills.Construction.BlockAverages
variable {F : BlockFrame}
def QuarticBoundAcrossLevelsWithRate : Prop :=
  ∀ (L W : ℕ) (K c0 : ℝ), Odd L → 5 ≤ L → 0 ≤ K → 0 < c0 → ∃ c1 : ℝ, 0 < c1 ∧
    ∀ (F : BlockFrame) (D : Finset F.Cell) (a : (j : ℕ) → F.Site j → Fin 4 → ℝ)
      (m e : (j : ℕ) → F.Site (j + 1) → Fin 4 → ℝ) (δ B : ℝ),
      F.blockSide = L → D.card ≤ W → 0 ≤ δ → δ ≤ c1 → 0 ≤ B → B ≤ c1 →
      (∀ j x i, 0 ≤ a j x i) → (∀ j x i, 0 ≤ m j x i) → (∀ j x i, 0 ≤ e j x i) →
      Real.sqrt (Real.sqrt (∑ b ∈ innerBonds D 0, a 0 b.1 b.2 ^ 4)) ≤ B →
      (∀ j, j + 1 < F.top → Real.sqrt (∑ c ∈ innerBonds D (j + 1), m j c.1 c.2 ^ 2) ≤ B) →
      (∀ j, j + 1 < F.top → Real.sqrt (Real.sqrt (∑ c ∈ innerBonds D (j + 1), e j c.1 c.2 ^ 4)) ≤ δ) →
      (∀ j, j + 1 < F.top → ∀ c ∈ innerBonds D (j + 1), ∀ t : ℝ, 0 ≤ t → t ≤ c0 → m j c.1 c.2 ≤ c0 →
        BoundedOnAdjacentBlocks (a j) c t →
        a (j + 1) c.1 c.2 ≤ m j c.1 c.2 + lineBlockAverage (a j) c +
          K * (t ^ 2 + (e j c.1 c.2 + m j c.1 c.2) * t)) →
      ∀ j, j < F.top → Real.sqrt (Real.sqrt (∑ b ∈ innerBonds D j, a j b.1 b.2 ^ 4)) ≤ 4 * B
end YangMills.Construction.BlockAverages
end
