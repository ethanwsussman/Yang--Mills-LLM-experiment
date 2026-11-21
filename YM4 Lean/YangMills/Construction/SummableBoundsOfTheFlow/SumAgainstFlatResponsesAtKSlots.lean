import YangMills.Construction.ColdStepAtMirrorFrames.SumAgainstThreeFlatResponses
import Mathlib
set_option autoImplicit false
noncomputable section
namespace YangMills.Construction
open BlockAverages ColdStepAtMirrorFrames
namespace Interpolation
variable {F : BlockFrame}
def flatResponseSum {k : ℕ} (δ : ℝ) (Y : F.Cell) (W : Fin k → LevelForm F F.depth) : ℝ :=
  ∑ y ∈ blockFineSites Y, ∑ b ∈ Fintype.piFinset (fun _ : Fin k => fineBonds F),
    (torusDecayFactor F.blockSide δ (bondSpan y b))⁻¹ *
      ∏ i, |localAxialGauge (Real.sqrt F.blockSide) y (W i) (b i).1 (b i).2|
def multilinearResponseBound : Prop :=
  ∀ a : ℝ, 1 ≤ a → ∃ del : ℝ, 0 < del ∧ ∃ L₀ : ℕ, ∀ (F : BlockFrame) (δ : ℝ) (Y : F.Cell) (k : ℕ)
    (c : Fin k → F.Site F.top × Fin 4) (B : Fin k → FormChain F) (W : Fin k → LevelForm F F.depth),
    3 ≤ k → k ≤ 6 → Odd F.blockSide → L₀ ≤ F.blockSide → IsLargeCubicTorus F → 0 < δ → δ ≤ del / 64 →
    (∀ i, IsFlatChain a (c i) (B i)) → (∀ i, IsAxialResponse (c i) (B i) (W i)) →
    flatResponseSum δ Y W ≤ (F.blockSide : ℝ) ^ (-(1 / 4 : ℝ)) / torusDecayFactor F.blockSide δ (bondSpan Y c)
end Interpolation
end YangMills.Construction
end
