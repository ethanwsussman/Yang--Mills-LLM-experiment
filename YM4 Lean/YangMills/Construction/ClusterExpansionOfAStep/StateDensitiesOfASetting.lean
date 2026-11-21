import YangMills.Construction.ClusterExpansionOfAStep.DensitiesOfASetting
import Mathlib
set_option autoImplicit false
noncomputable section
namespace YangMills.Construction.ClusterExpansionOfAStep
open StepSettings
def BlockDensitiesMeasurableBounded : Prop :=
  ∀ (R : StepSetup) (n : ℕ) [NeZero n] (s : ChartSetting R n), R.params.Admissible → 1 ≤ R.params.E →
    0 < R.coupling → 4 * R.params.n₀ + 2 ^ 16 ≤ R.range → R.params.side + 2 ≤ R.range → R.HasExpansions →
    R.params.n₀ ≤ n → s.IsAdmissible →
    (∀ Y, ∃ G : FreeCoords s.free → ℝ, Measurable G ∧ ∀ η, s.InBalls η → G η = s.blockDensityAt Y η) ∧
      ∃ M : ℝ, ∀ η, s.InBalls η → ∀ Y, |s.blockDensityAt Y η| ≤ M
end YangMills.Construction.ClusterExpansionOfAStep
end
