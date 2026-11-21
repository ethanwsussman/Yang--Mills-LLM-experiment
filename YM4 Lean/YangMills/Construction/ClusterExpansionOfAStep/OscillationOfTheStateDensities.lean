import YangMills.Construction.ClusterExpansionOfAStep.DensitiesOfASetting
import Mathlib
set_option autoImplicit false
noncomputable section
namespace YangMills.Construction.ClusterExpansionOfAStep
open TorusFields StepSettings ColdStepAtMirrorFrames
def BlockDensityOscillationBound : Prop :=
  ∀ (R : StepSetup) (n : ℕ) [NeZero n] (s : ChartSetting R n), R.params.Admissible → 1 ≤ R.params.E →
    0 < R.coupling → 4 * R.params.n₀ + 2 ^ 16 ≤ R.range → R.params.side + 2 ≤ R.range → R.HasExpansions →
    R.params.n₀ ≤ n → s.IsAdmissible →
    ∀ (Y : TorusSite n) (η η' : FreeCoords s.free), s.InBalls η → s.InBalls η' →
      |s.blockDensityAt Y η - s.blockDensityAt Y η'| ≤ (R.params.side : ℝ) ^ 4 * (4 * R.params.E + 2)
end YangMills.Construction.ClusterExpansionOfAStep
end
