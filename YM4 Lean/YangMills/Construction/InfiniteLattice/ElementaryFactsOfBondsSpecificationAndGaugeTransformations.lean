import YangMills.Construction.InfiniteLattice.ElementaryFactsOfBonds
import Mathlib
set_option autoImplicit false
noncomputable section
namespace YangMills.Construction
namespace InfiniteLattice
def ElementaryLatticeFacts : Prop :=
  ∀ (a β : ℝ) (ha : 0 < a), 0 < β →
    GaugeFieldsAreLinkFamilies ha ∧ PlaquetteProperties a ∧
      SpecificationProperties ha β ∧ LocalFunctionProperties a ∧
      GaugeTransformProperties a ∧ PeriodicMeasuresCubicInvariance ha β ∧
      MeasurableIffDependsOnly a ∧ LatticeSymmetryProperties a ∧
      FiniteHaarIntegralsBounded a
end InfiniteLattice
end YangMills.Construction
