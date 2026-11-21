import YangMills.Construction.ResponseInTheExpansion.ObservablesOfTheGas
import YangMills.Construction.ResponseInTheExpansion.ResponseInASetting
import Mathlib
set_option autoImplicit false
noncomputable section
open MeasureTheory
namespace YangMills.Construction.ResponseInTheExpansion
def GasMeansMeasurable : Prop :=
  WeightedResponses.HoldsAtEveryStep fun _ R A => ∀ (n : ℕ) [NeZero n] (G : StepGas.GasGround R n), G.IsAdmissibleGround →
    (∀ (y : TorusFields.TorusSite (n * R.params.side))
        (h : WeightedResponses.PlaquetteWeight (WeightedResponses.fineSide R.params.side R.depth (n * R.params.side))),
      Measurable (restrictAdmissible G fun σ =>
        WeightedResponses.chartResponse A (WeightedResponses.configSetting G σ) y h)) ∧
    (∀ c : TorusFields.TorusBond n, Measurable (restrictAdmissible G fun σ =>
        WeightedResponses.chartBondScore (WeightedResponses.configSetting G σ) c)) ∧
    ∀ y : TorusFields.TorusSite (n * R.params.side), Measurable (restrictAdmissible G fun σ =>
        WeightedResponses.chartSiteScore A (WeightedResponses.configSetting G σ) y)
end YangMills.Construction.ResponseInTheExpansion
end
