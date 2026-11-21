import YangMills.Construction.InfiniteLattice.ConfigurationsAreFamiliesOnTheBondsAtEverySpacing
import YangMills.Construction.InfiniteLattice.ElementaryFactsOfBondsSpecificationAndGaugeTransformations
import YangMills.Construction.InfiniteLattice.FactsOfTheGaugeTransformationsAtEverySpacing
import YangMills.Construction.InfiniteLattice.FactsOfTheLatticeIsometriesAtEverySpacing
import YangMills.Construction.InfiniteLattice.FactsOfTheLocalFunctionsAtEverySpacing
import YangMills.Construction.InfiniteLattice.FactsOfThePlaquettesAtEverySpacing
import YangMills.Construction.InfiniteLattice.FactsOfTheSpecificationAtEverySpacing
import YangMills.Construction.InfiniteLattice.IntegralsOverFiniteProductsAreObservablesAtEverySpacing
import YangMills.Construction.InfiniteLattice.MeasurabilityIsDependenceOnVariablesAtEverySpacing
import YangMills.Construction.InfiniteLattice.PeriodicMeasuresHaveCubicPeriodsAtEverySpacing
import Mathlib
set_option autoImplicit false
namespace YangMills.Construction.InfiniteLattice
theorem elementaryLatticeFacts_of_properties
    (links : GaugeFieldsAreLinkFamiliesForAllSpacings)
    (faces : PlaquettePropertiesAllMeshes.Statement)
    (kernel : SpecificationPropertiesAtEveryMesh)
    (localFns : LocalFunctionPropertiesForAllSpacings)
    (gauge : GaugeTransformPropertiesForAllSpacings)
    (cubic : PeriodicMeasuresCubicInvarianceAllSpacings)
    (meas : MeasurableIffDependsOnlyAllSpacings)
    (symm : LatticeSymmetryPropertiesAtEverySpacing)
    (haar : FiniteHaarIntegralsBoundedAtAllSpacings) :
    ElementaryLatticeFacts :=
  fun a β ha hβ =>
    ⟨links a ha, faces a ha, kernel a β ha hβ, localFns a ha, gauge a ha,
      cubic a β ha hβ, meas a ha, symm a ha, haar a ha⟩
end YangMills.Construction.InfiniteLattice
