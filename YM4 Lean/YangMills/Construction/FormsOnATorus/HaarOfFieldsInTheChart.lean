import YangMills.Construction.ClusterExpansionOfAStep.FieldsOnATorus
import YangMills.Construction.FormsOnATorus.GaugeActionDefs
import Mathlib
set_option autoImplicit false
noncomputable section
open MeasureTheory
open scoped Quaternion
namespace YangMills.Construction.GaugeCharts
open BlockAverages TorusFields
def HaarOnFieldsInHemisphereChart : Prop :=
  ∀ [MeasurableSpace imaginaryQuaternions] [BorelSpace imaginaryQuaternions]
    (μ : Measure imaginaryQuaternions) [μ.IsAddHaarMeasure] (κ : Type) [Fintype κ] [DecidableEq κ],
    ∃ c : ℝ, 0 < c ∧ ∀ (V : κ → UnitQuaternion) (Φ : (κ → UnitQuaternion) → ENNReal), Measurable Φ →
      ∫⁻ w in {w : κ → UnitQuaternion | ∀ b, 0 < ((w b * (V b)⁻¹ : UnitQuaternion) : ℍ[ℝ]).re},
          Φ w ∂(Measure.pi fun _ : κ => haarUnit) =
        ENNReal.ofReal c * ∫⁻ y in {y : κ → imaginaryQuaternions | ∀ b, ‖y b‖ < 1},
          Φ (hemisphereChartField V y) * ENNReal.ofReal (∏ b, hemisphereDensity (y b))
            ∂(Measure.pi fun _ : κ => μ)
end YangMills.Construction.GaugeCharts
end
