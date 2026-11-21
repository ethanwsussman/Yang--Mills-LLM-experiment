import YangMills.Construction.InfiniteLattice.IntegralsOverFiniteProductsAreObservablesAtEverySpacing
import YangMills.Construction.InfiniteLattice.SpaceOfConfigurationsOnTheInfiniteLatticeProof
import Mathlib
set_option autoImplicit false
open MeasureTheory Set Filter TopologicalSpace
noncomputable section
namespace YangMills.Construction.InfiniteLattice
namespace FiniteHaarIntegrals
theorem secondCountable_specialUnitary :
    SecondCountableTopology Matrices.ComplexMatrix2.specialUnitary := by apply _root_.YangMills.Construction.InfiniteLattice.WilsonOperator.secondCountable_specialUnitary <;> assumption
theorem secondCountable_gaugeField (a : ℝ) : SecondCountableTopology (GaugeField a) := by apply _root_.YangMills.Construction.InfiniteLattice.GaugeFieldSpace.secondCountableTopology_gaugeField <;> assumption
theorem nonempty_gaugeField (a : ℝ) : Nonempty (GaugeField a) :=
  ⟨⟨fun _ => 1, fun _ => by simp⟩⟩
theorem finiteHaarIntegralsBounded_of_spacing (a : ℝ) : FiniteHaarIntegralsBounded a := by
  intro S _ Φ hΦ hC
  have := secondCountable_specialUnitary
  have := secondCountable_gaugeField a
  have := nonempty_gaugeField a
  have : IsProbabilityMeasure (Matrices.ComplexMatrix2.haarPi S) := by
    unfold Matrices.ComplexMatrix2.haarPi
    infer_instance
  have hb : (inferInstance :
      MeasurableSpace ((S → Matrices.ComplexMatrix2.specialUnitary) × GaugeField a)) =
      borel ((S → Matrices.ComplexMatrix2.specialUnitary) × GaugeField a) :=
    BorelSpace.measurable_eq
  have hm : Measurable Φ := hΦ.mono hb.ge le_rfl
  have hsm : StronglyMeasurable
      fun q : GaugeField a × (S → Matrices.ComplexMatrix2.specialUnitary) => Φ (q.2, q.1) :=
    (hm.comp measurable_swap).stronglyMeasurable
  have hint : StronglyMeasurable fun U => ∫ g, Φ (g, U) ∂Matrices.ComplexMatrix2.haarPi S :=
    hsm.integral_prod_right'
  obtain ⟨C, hC⟩ := hC
  have hbdd : BddAbove (range fun q => ‖Φ q‖) := ⟨C, by
    rintro _ ⟨q, rfl⟩
    exact hC q⟩
  have hle : ∀ q, ‖Φ q‖ ≤ ⨆ q, ‖Φ q‖ := le_ciSup hbdd
  have hnorm : ∀ U, ‖∫ g, Φ (g, U) ∂Matrices.ComplexMatrix2.haarPi S‖ ≤ ⨆ q, ‖Φ q‖ :=
    fun U => by
      have h := norm_integral_le_of_norm_le_const (μ := Matrices.ComplexMatrix2.haarPi S)
        (f := fun g => Φ (g, U)) (Eventually.of_forall fun g => hle (g, U))
      simpa using h
  refine ⟨⟨hint.measurable, _, hnorm⟩, ciSup_le hnorm, fun hc => ?_⟩
  refine continuous_of_dominated (bound := fun _ => ⨆ q, ‖Φ q‖) (fun U => ?_)
    (fun U => Eventually.of_forall fun g => hle (g, U)) (integrable_const _)
    (Eventually.of_forall fun g => ?_)
  · exact (hc.comp (Continuous.prodMk_left U)).aestronglyMeasurable
  · exact hc.comp (Continuous.prodMk_right g)
end FiniteHaarIntegrals
theorem finiteHaarIntegralsBoundedAtAllSpacings_holds :
    FiniteHaarIntegralsBoundedAtAllSpacings :=
  fun a _ => FiniteHaarIntegrals.finiteHaarIntegralsBounded_of_spacing a
end YangMills.Construction.InfiniteLattice
