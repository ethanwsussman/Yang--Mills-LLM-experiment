import YangMills.Construction.ResponseInTheExpansion.ResponseInASetting
import YangMills.Construction.ResponseInTheExpansion.SupportsAlongTheLevels
import Mathlib
set_option autoImplicit false
noncomputable section
open MeasureTheory
namespace YangMills.Construction.StateLaws
variable {n : ℕ} [NeZero n]
def settingMean {R : StepSettings.StepSetup} (s : StepSettings.ChartSetting R n)
    (Q : ResponseInTheExpansion.StateFunction R (n * R.params.side)) : ℝ :=
  StepSettings.weightedMean (WeightedResponses.chartDensity s) fun η => Q (s.field η) s.support s.labelling
end YangMills.Construction.StateLaws
end
