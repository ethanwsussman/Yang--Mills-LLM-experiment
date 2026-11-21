import YangMills.Construction.ColdStepAtMirrorFrames.SumAgainstThreeFlatResponses
import Mathlib
set_option autoImplicit false
noncomputable section
namespace YangMills.Construction
open BlockAverages
namespace WeightedResponses
open ColdStepAtMirrorFrames
def TwoGaugedResponseSumBound : Prop :=
  ∀ a : ℝ, 1 ≤ a → ∃ ε Ca : ℝ, 0 < ε ∧ 0 < Ca ∧ ∃ L₀ : ℕ, ∀ (F : BlockFrame) (δ : ℝ) (Y : F.Cell)
    (c : Fin 2 → F.Site F.top × Fin 4) (B : Fin 2 → FormChain F) (A : Fin 2 → LevelForm F F.depth), Odd F.blockSide →
    L₀ ≤ F.blockSide → IsLargeCubicTorus F → 0 < δ → δ ≤ ε / 64 → (∀ i, IsFlatChain a (c i) (B i)) →
    (∀ i, IsAxialResponse (c i) (B i) (A i)) →
    ∑ y ∈ blockFineSites Y, ∑ b₁ ∈ fineBonds F, ∑ b₂ ∈ fineBonds F,
      (torusDecayFactor F.blockSide δ (bondSpan y ![b₁, b₂]))⁻¹ *
        |localAxialGauge (Real.sqrt F.blockSide) y (A 0) b₁.1 b₁.2| *
        |localAxialGauge (Real.sqrt F.blockSide) y (A 1) b₂.1 b₂.2| ≤
      Ca * (F.blockSide : ℝ) ^ (50 / 640 : ℝ) / torusDecayFactor F.blockSide δ (bondSpan Y c)
end WeightedResponses
end YangMills.Construction
end
