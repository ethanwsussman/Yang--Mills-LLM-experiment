import YangMills.Construction.ClusterExpansionOfAStep.FieldsOnATorus
import YangMills.Construction.FormsOnATorus.GaugeActionDefs
import Mathlib
set_option autoImplicit false
noncomputable section
open MeasureTheory
open scoped Quaternion
namespace YangMills.Construction.GaugeCharts
open BlockAverages TorusFields
def HaarOnHemisphereChart : Prop :=
  ∀ [MeasurableSpace imaginaryQuaternions] [BorelSpace imaginaryQuaternions]
    (μ : Measure imaginaryQuaternions) [μ.IsAddHaarMeasure], ∃ c : ℝ, 0 < c ∧
    ∀ f : UnitQuaternion → ENNReal, Measurable f →
      ∫⁻ g in {g : UnitQuaternion | 0 < (g : ℍ[ℝ]).re}, f g ∂haarUnit =
        ENNReal.ofReal c * ∫⁻ y in {y : imaginaryQuaternions | ‖y‖ < 1},
          f (hemisphereUnit y) * ENNReal.ofReal (hemisphereDensity y) ∂μ
end YangMills.Construction.GaugeCharts
end
