import YangMills.Construction.ClusterExpansionOfAStep.FieldsOnATorus
import YangMills.Construction.FormsOnATorus.GaugeActionDefs
import Mathlib
set_option autoImplicit false
noncomputable section
open MeasureTheory
open scoped Quaternion
namespace YangMills.Construction.GaugeCharts
open BlockAverages TorusFields
def FreeGaugeActionChangeOfVariables : Prop :=
  ∀ [MeasurableSpace imaginaryQuaternions] [BorelSpace imaginaryQuaternions]
    (ι κ S : Type) [Fintype ι] [DecidableEq ι] [Fintype κ] [DecidableEq κ]
    [NormedAddCommGroup S] [NormedSpace ℝ S] [FiniteDimensional ℝ S] [MeasurableSpace S] [BorelSpace S]
    (src tgt : κ → Option ι) (V : κ → UnitQuaternion) (e : S →ₗ[ℝ] (κ → imaginaryQuaternions))
    (Q : (κ → imaginaryQuaternions) →ₗ[ℝ] ((ι → imaginaryQuaternions) × S))
    (Z : Set S) (μ : Measure S) [μ.IsAddHaarMeasure],
    IsCompact Z →
    (∀ ζ ∈ Z, ∀ b, ‖e ζ b‖ < 1) →
    chartLinearization src tgt V e 0 ∘ₗ Q = LinearMap.id →
    Q ∘ₗ chartLinearization src tgt V e 0 = LinearMap.id →
    Set.InjOn (fun p : (ι → UnitQuaternion) × S =>
      gaugeTransform src tgt p.1 (hemisphereChartField V (e p.2))) (Set.univ ×ˢ Z) →
    ∃ c : ℝ, 0 < c ∧ ∀ Φ : (κ → UnitQuaternion) → ENNReal, Measurable Φ →
      ∫⁻ w in (fun p : (ι → UnitQuaternion) × S =>
          gaugeTransform src tgt p.1 (hemisphereChartField V (e p.2))) '' (Set.univ ×ˢ Z),
          Φ w ∂(Measure.pi fun _ : κ => haarUnit) =
        ENNReal.ofReal c * ∫⁻ g, ∫⁻ ζ in Z, Φ (gaugeTransform src tgt g (hemisphereChartField V (e ζ))) *
          ENNReal.ofReal (chartJacobian src tgt V e Q (e ζ)) ∂μ ∂(Measure.pi fun _ : ι => haarUnit)
end YangMills.Construction.GaugeCharts
end
