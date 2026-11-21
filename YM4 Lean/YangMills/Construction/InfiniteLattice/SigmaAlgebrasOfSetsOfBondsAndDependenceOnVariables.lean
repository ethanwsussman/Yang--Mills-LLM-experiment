import YangMills.Construction.InfiniteLattice.ObservablesHypercubicLatticeMapsAndHyperplanes
import YangMills.Construction.InfiniteLattice.PositiveLinksAndCylinderFunctions
import YangMills.Construction.InfiniteLattice.SpecificationGaugeTransformationsAndClassesOfMeasures
import Mathlib
set_option autoImplicit false
open MeasureTheory
open scoped ComplexConjugate
noncomputable section
namespace YangMills.Construction.InfiniteLattice
def LinkSigmaAndDependence : Prop :=
  ∀ a : ℝ, 0 < a →
    (∀ M M' : Set (Link a), IsLinkSet M → IsLinkSet M' →
      ∀ F : GaugeField a → ℂ, IsBoundedObservable F →
        (Measurable[linkSigma M] F ↔ DependsOnlyOn M F) ∧
        (DependsOnlyOn M F → DependsOnlyOn M' F →
          DependsOnlyOn (M ∩ M') F)) ∧
    (∀ S : Set AmbientSpace, regionObservables a S =
      {F | IsBoundedObservable F ∧ Measurable[linkSigma (positiveLinksWithin a S)] F}) ∧
    (∀ (S S' : Set AmbientSpace) (F : GaugeField a → ℂ), IsBoundedObservable F →
      IsRegionMeasurable S F → IsRegionMeasurable S' F → IsRegionMeasurable (S ∩ S') F)
end YangMills.Construction.InfiniteLattice
end
