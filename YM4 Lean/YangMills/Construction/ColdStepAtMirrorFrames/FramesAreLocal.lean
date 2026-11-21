import YangMills.Construction.ColdStepAtMirrorFrames.FramesAgainstTheLeastField
import Mathlib
set_option autoImplicit false
noncomputable section
open YangMills.Construction.BlockAverages
namespace YangMills.Construction.ColdStepAtMirrorFrames
def framesLocalStatement : Prop :=
  ∀ (a : ℝ) (L : ℕ) (c : ColdChainParameters), 1 ≤ a → Odd L → c.Admissible a L → ∃ C : ℝ, 1 ≤ C ∧
    ∀ (σ : ℝ) (m : ℕ) (F F' : BlockFrame) (V : F.GaugeField F.top) (V' : F'.GaugeField F'.top)
      (Y : F.Cell) (Y' : F'.Cell) (r : ℕ),
      0 < σ → 5 / 4 * σ ≤ c.s₀ → 16 ≤ m → IsBlockTorus L F → IsBlockTorus L F' → F'.depth = F.depth →
      IsSmallCurvature (5 / 4 * σ) V → IsSmallCurvature (5 / 4 * σ) V' →
      AgreeOnBall (finiteCells F) V (finiteCells F') V' Y Y' r →
      ∀ star, FrameLocality star a c.ρA c.δ₂ C σ m V V' Y Y' r
end YangMills.Construction.ColdStepAtMirrorFrames
end
