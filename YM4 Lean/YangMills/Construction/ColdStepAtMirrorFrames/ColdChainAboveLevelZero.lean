import YangMills.Construction.ColdStepAtMirrorFrames.NumbersOfTheColdChainFormForm
import YangMills.Construction.ColdStepAtMirrorFrames.PropertiesOfTheLowerLevelChain
import Mathlib
set_option autoImplicit false
noncomputable section
open YangMills.Construction.BlockAverages
namespace YangMills.Construction.ColdStepAtMirrorFrames
def ColdEstimatesAtPositiveDepth : Prop :=
  ∀ (a : ℝ) (L : ℕ) (c : ColdChainParameters), 1 ≤ a → Odd L → 2 ^ 40 ≤ L → c.Admissible a L →
    ∃ N : ℕ → ℝ, (∀ k, 0 < N k) ∧
      (∀ (F : BlockFrame) (s : ℝ) (W : F.GaugeField F.depth), IsBlockTorus L F → 1 ≤ F.depth → 0 < s →
        s ≤ c.σA → IsSmallCurvature s W → ColdEstimatesBelow a c.δ₁ s N W) ∧
      ∀ (F F' : BlockFrame) (s : ℝ) (W : F.GaugeField F.depth) (W' : F'.GaugeField F'.depth)
        (y : F.Site F.depth) (y' : F'.Site F'.depth) (r : ℕ), IsBlockTorus L F → IsBlockTorus L F' →
        1 ≤ F.depth → F'.depth = F.depth → 0 < s → s ≤ c.σA →
        IsSmallCurvature s W → IsSmallCurvature s W' → AgreeOnBox W W' y y' r →
        ColdComparisonBelow a c.δ₁ c.δ₂ s c.s₀ N W W' y y' r
end YangMills.Construction.ColdStepAtMirrorFrames
end
