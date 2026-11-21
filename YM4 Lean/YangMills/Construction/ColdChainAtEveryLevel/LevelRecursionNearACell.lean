import YangMills.Construction.ColdChainAtEveryLevel.LevelsAndFields
import Mathlib
set_option autoImplicit false
noncomputable section
open scoped Quaternion
namespace YangMills.Construction.BlockAverages
variable {F : BlockFrame}
def lineBlockAverage {j : ℕ} (f : F.Site j → Fin 4 → ℝ) (c : F.Site (j + 1) × Fin 4) : ℝ :=
  (1 / (F.blockSide : ℝ) ^ 4) * ∑ h ∈ centredCube F.blockSide, ∑ r ∈ Finset.range F.blockSide,
    f (refineSite c.1 + siteOfCoords j h + (r : ℤ) • unitStep j c.2) c.2
def BoundedOnAdjacentBlocks {j : ℕ} (f : F.Site j → Fin 4 → ℝ) (c : F.Site (j + 1) × Fin 4)
    (t : ℝ) : Prop :=
  (∀ h ∈ centredCube F.blockSide, ∀ k, h + Pi.single k 1 ∈ centredCube F.blockSide →
    f (refineSite c.1 + siteOfCoords j h) k ≤ t ∧
      f (refineSite (c.1 + unitStep (j + 1) c.2) + siteOfCoords j h) k ≤ t) ∧
  ∀ h ∈ centredCube F.blockSide, ∀ r ∈ Finset.range F.blockSide,
    f (refineSite c.1 + siteOfCoords j h + (r : ℤ) • unitStep j c.2) c.2 ≤ t
def UniformQuarticBoundAcrossLevels : Prop :=
  ∀ (L W : ℕ) (K c0 : ℝ), Odd L → 5 ≤ L → 0 ≤ K → 0 < c0 → ∃ c1 : ℝ, 0 < c1 ∧
    ∀ (F : BlockFrame) (D : Finset F.Cell) (a : (j : ℕ) → F.Site j → Fin 4 → ℝ)
      (m : (j : ℕ) → F.Site (j + 1) → Fin 4 → ℝ) (s B : ℝ),
      F.blockSide = L → D.card ≤ W → 0 ≤ s → s ≤ c1 → 0 ≤ B → B ≤ c1 →
      (∀ j x i, 0 ≤ a j x i) → (∀ j x i, 0 ≤ m j x i) →
      Real.sqrt (Real.sqrt (∑ b ∈ innerBonds D 0, a 0 b.1 b.2 ^ 4)) ≤ B →
      (∀ j, j + 1 < F.top → Real.sqrt (∑ c ∈ innerBonds D (j + 1), m j c.1 c.2 ^ 2) ≤ B) →
      (∀ j, j + 1 < F.top → ∀ c ∈ innerBonds D (j + 1), ∀ t : ℝ, 0 ≤ t → t ≤ c0 →
        m j c.1 c.2 ≤ c0 → BoundedOnAdjacentBlocks (a j) c t →
        a (j + 1) c.1 c.2 ≤ m j c.1 c.2 + lineBlockAverage (a j) c +
          K * (t ^ 2 + (s * ((1 / (F.blockSide : ℝ)) ^ (F.top - (j + 1))) ^ 2 + m j c.1 c.2 +
            s * ((1 / (F.blockSide : ℝ)) ^ (F.top - (j + 1))) ^ 3) * t)) →
      ∀ j, j < F.top → Real.sqrt (Real.sqrt (∑ b ∈ innerBonds D j, a j b.1 b.2 ^ 4)) ≤ 4 * B
end YangMills.Construction.BlockAverages
end
