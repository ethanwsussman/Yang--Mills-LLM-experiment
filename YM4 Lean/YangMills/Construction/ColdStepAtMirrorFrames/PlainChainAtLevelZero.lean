import YangMills.Construction.ColdStepAtMirrorFrames.PropertiesOfTheLowerLevelChain
import Mathlib
set_option autoImplicit false
noncomputable section
open YangMills.Construction.BlockAverages
namespace YangMills.Construction.ColdStepAtMirrorFrames
def WilsonActionColdEstimates : Prop :=
  ∃ N : ℕ → ℝ, (∀ k, 0 < N k) ∧ ∀ (a δ δ₂ s₀ : ℝ), 0 ≤ δ → δ ≤ 1 / 8 → 0 ≤ δ₂ →
    (∀ (F : BlockFrame) (s : ℝ) (W : F.GaugeField F.depth), F.depth = 0 → Odd F.blockSide →
      IsLargeCubicTorus F → 0 < s →
      IsSmallCurvature s W → ColdEstimatesBelow a δ s N W) ∧
    ∀ (F F' : BlockFrame) (s : ℝ) (W : F.GaugeField F.depth) (W' : F'.GaugeField F'.depth)
      (y : F.Site F.depth) (y' : F'.Site F'.depth) (r : ℕ),
      F.depth = 0 → F'.depth = 0 → Odd F.blockSide → Odd F'.blockSide → IsLargeCubicTorus F →
      IsLargeCubicTorus F' → 0 < s →
      IsSmallCurvature s W → IsSmallCurvature s W' → AgreeOnBox W W' y y' r →
      ColdComparisonBelow a δ δ₂ s s₀ N W W' y y' r
end YangMills.Construction.ColdStepAtMirrorFrames
end
