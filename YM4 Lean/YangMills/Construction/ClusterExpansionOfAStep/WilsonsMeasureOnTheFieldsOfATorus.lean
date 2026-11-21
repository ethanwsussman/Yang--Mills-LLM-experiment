import YangMills.Construction.ClusterExpansionOfAStep.FieldsAsConfigurations
import YangMills.Construction.ClusterExpansionOfAStep.WilsonWeightHasAnExpansion
import YangMills.Construction.Lattice.WilsonGibbsMeasure
import Mathlib
set_option autoImplicit false
noncomputable section
open MeasureTheory
open scoped ENNReal
namespace YangMills.Construction
namespace ClusterExpansionOfAStep
open SoftAverages
structure TorusFieldsAreGaugeFields (L m K n : ℕ) [NeZero n] : Prop where
  siteBijective : Function.Bijective (periodicLatticeSite (n := n) L m (K : ℤ))
  torusSite_periodicLatticeSite : ∀ x : TorusFields.TorusSite n,
    torusSiteOfLatticeSite n (periodicLatticeSite L m (K : ℤ) x) = x
  gaugeField_injective : Function.Injective (gaugeFieldOfTorusField (n := n) L m (K : ℤ))
  range_gaugeField : Set.range (gaugeFieldOfTorusField (n := n) L m (K : ℤ)) =
    PeriodicLattice.compactGaugeFields L m (K : ℤ)
  gaugeField_forwardFrom : ∀ (U : TorusFields.TorusField n) (x : TorusFields.TorusSite n) (μ : Fin 4),
    gaugeFieldOfTorusField L m (K : ℤ) U (PeriodicLattice.Bond.forwardFrom (periodicLatticeSite L m (K : ℤ) x) μ) =
      quaternionToMatrix (U x μ : Quaternion ℝ)
  plaquetteHolonomy_eq : ∀ (U : TorusFields.TorusField n) (x : TorusFields.TorusSite n) (μ ν : Fin 4) (hμν : μ < ν),
    PeriodicLattice.plaquetteHolonomy (gaugeFieldOfTorusField L m (K : ℤ) U)
        ⟨periodicLatticeSite L m (K : ℤ) x, μ, ν, hμν⟩ =
      quaternionToMatrix (TorusFields.holonomy U x μ ν : Quaternion ℝ)
  gaugeTransform_eq : ∀ (g : TorusFields.TorusSite n → BlockAverages.UnitQuaternion) (U : TorusFields.TorusField n),
    gaugeFieldOfTorusField L m (K : ℤ) (TorusFields.gaugeTransform g U) =
      PeriodicLattice.gaugeTransform (fun s => quaternionToMatrix (g (torusSiteOfLatticeSite n s) : Quaternion ℝ))
        (gaugeFieldOfTorusField L m (K : ℤ) U)
  wilsonAction_eq : ∀ U : TorusFields.TorusField n,
    PeriodicLattice.wilsonAction (gaugeFieldOfTorusField L m (K : ℤ) U) = TorusFields.wilsonAction Finset.univ U
  measurable_gaugeField : Measurable (gaugeFieldOfTorusField (n := n) L m (K : ℤ))
  map_fieldHaar : (TorusFields.fieldHaar n).map (gaugeFieldOfTorusField L m (K : ℤ)) =
    PeriodicLattice.productHaarMeasure L m (K : ℤ)
  boltzmannWeight_eq : ∀ (β : ℝ) (U : TorusFields.TorusField n),
    PeriodicLattice.boltzmannWeight β (gaugeFieldOfTorusField L m (K : ℤ) U) = TorusLumps.wilsonWeight β n U
  partitionFunction_eq : ∀ β : ℝ, PeriodicLattice.partitionFunction L m K β =
    ∫ U, TorusLumps.wilsonWeight β n U ∂(TorusFields.fieldHaar n)
  wilsonGibbsMeasure_eq : ∀ β : ℝ, PeriodicLattice.wilsonGibbsMeasure L m K β =
    (ENNReal.ofReal (∫ U, TorusLumps.wilsonWeight β n U ∂(TorusFields.fieldHaar n)))⁻¹ •
      ((TorusFields.fieldHaar n).withDensity fun U => ENNReal.ofReal (TorusLumps.wilsonWeight β n U)).map
        (gaugeFieldOfTorusField L m (K : ℤ))
def WilsonMeasureOnTorusFields : Prop :=
  ∀ (L m K n : ℕ) [NeZero n], n = 2 * L ^ (m + K) → 2 < n → TorusFieldsAreGaugeFields L m K n
end ClusterExpansionOfAStep
end YangMills.Construction
end
