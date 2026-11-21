import YangMills.Construction.ClusterExpansionOfAStep.OffsetsOfABlock
import Mathlib
set_option autoImplicit false
noncomputable section
namespace YangMills.Construction
open TorusFields TorusLumps StepSettings BlockOffsets BlockAverages LumpContours
namespace StepSettings
def BlockDensitiesClose : Prop :=
  ∀ (R : StepSetup) (n n' : ℕ) [NeZero n] [NeZero n'] (s : ChartSetting R n) (s' : ChartSetting R n')
    (Y : TorusSite n) (Y' : TorusSite n') (m k : ℕ) (η : FreeCoords s.free) (η' : FreeCoords s'.free),
    R.params.Admissible → R.HasExpansions → R.params.n₀ ≤ n → R.params.n₀ ≤ n' → s.IsAdmissible →
    s'.IsAdmissible → SettingsAgreeNear s s' Y Y' m →
    2 ≤ k → k ≤ m → (R.range : ℝ) / 64 ≤ ((R.params.side * k - 2 * R.params.side : ℕ) : ℝ) →
    CoordsAgreeNear s s' Y Y' k η η' →
    s.InBalls η → s'.InBalls η' →
    |s.blockDensityAt Y η - s'.blockDensityAt Y' η'| ≤
      (R.params.side : ℝ) ^ 4 *
        Real.exp (-R.params.decayRate * ((R.params.side * k - 2 * R.params.side : ℕ) : ℝ))
end StepSettings
end YangMills.Construction
end
