import YangMills.Construction.ColdStepAtMirrorFrames.MirrorFrameAgainstTheChain
import Mathlib
set_option autoImplicit false
noncomputable section
open YangMills.Construction.BlockAverages
namespace YangMills.Construction.ColdStepAtMirrorFrames
def framesSmallStatement : Prop :=
  ∀ (a : ℝ) (L : ℕ) (c : ColdChainParameters), 1 ≤ a → Odd L → c.Admissible a L → ∃ C σ₁ : ℝ, 1 ≤ C ∧ 0 < σ₁ ∧
    ∀ (σ : ℝ) (m : ℕ) (F : BlockFrame) (V : F.GaugeField F.top), 0 < σ → σ ≤ σ₁ → 16 ≤ m →
      frameDecayBound (frameBoundConstant c) c.δ₂ m ≤ 2⁻¹ ^ 10 * σ → IsBlockTorus L F →
      IsSmallCurvature (5 / 4 * σ) V →
      (∀ star, FrameSmallness star a c.ρA c.δ₂ c.κ₂ C σ c.Kk m V) ∧
      ∀ w : F.Site F.depth → Fin 4 → imaginaryQuaternions, (∀ b ∈ chordBonds (finiteCells F),
        ‖w b.1 b.2 - minimizingCoordinates a (finiteCells F) V c.ρA b.1 b.2‖ ≤ σ / 1024) →
        IsSmallCurvature (41 / 64 * σ) (chartedField w V)
end YangMills.Construction.ColdStepAtMirrorFrames
end
