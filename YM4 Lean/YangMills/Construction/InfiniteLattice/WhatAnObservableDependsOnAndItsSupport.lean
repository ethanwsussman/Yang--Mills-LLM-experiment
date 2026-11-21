import YangMills.Construction.InfiniteLattice.ObservablesHypercubicLatticeMapsAndHyperplanes
import YangMills.Construction.InfiniteLattice.SpecificationGaugeTransformationsAndClassesOfMeasures
import Mathlib
set_option autoImplicit false
noncomputable section
namespace YangMills.Construction.InfiniteLattice
def ObservableDependence.Statement : Prop :=
  ∀ (F : GaugeField 1 → ℂ), IsBoundedObservable F →
  ∀ (M M' : Set (Link 1)), IsLinkSet M → IsLinkSet M' → ∀ O : Set AmbientSpace,
    (F ∈ regionObservables 1 O →
      DependsOnlyOn {l | l ∈ positiveLinks 1 ∧ LinksLieIn {l} O} F) ∧
    (LinksLieIn M O → DependsOnlyOn M F → F ∈ regionObservables 1 O) ∧
    (DependsOnlyOn M F → DependsOnlyOn M' F →
      DependsOnlyOn (M ∩ M') F) ∧
    (IsLocalObservable F ↔ ∃ M₀ : Set (Link 1), IsLinkSet M₀ ∧ M₀.Finite ∧
      DependsOnlyOn M₀ F) ∧
    (IsLocalObservable F →
      IsLeast {N : Set (Link 1) | IsLinkSet N ∧ DependsOnlyOn N F}
        (observableSupport F) ∧ (observableSupport F).Finite) ∧
    (IsLocalObservable F →
      (F ∈ regionObservables 1 O ↔ LinksLieIn (observableSupport F) O) ∧
      (observableSupport F = ∅ ↔ ∃ c : ℂ, ∀ U, F U = c))
end YangMills.Construction.InfiniteLattice
