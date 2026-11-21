import YangMills.Construction.Lattice.ComplexOneStepObjectsFormedTogetherUnderATranslation
import YangMills.Construction.Lattice.CovarianceOfComplexFormsAndOneStepOperations
import YangMills.Construction.Lattice.CovarianceOfFormsAtComplexConfigurations
import YangMills.Construction.Lattice.CovarianceOfTheOneStepOperationsAtComplexConfigurations
import YangMills.Construction.Lattice.CovarianceOfTheRegionHessianAtComplexConfigurations
import YangMills.Construction.Lattice.HolomorphyOfTheSidesOfTheComplexOneStepIdentities
import Mathlib
set_option autoImplicit false
namespace YangMills.Construction.PeriodicLattice
theorem complexFormsAndStepOperationsCovariance
    (forms : ComplexTransportCovariance)
    (hessian : RegionHessianCovariance)
    (sides : HolomorphyOfStepIdentitySides)
    (operations : ComplexStepIsometryCovariance)
    (translation : TranslationPreservesComplexStepData) :
    ComplexFormsAndStepOperationsCovariance.Statement := by
  intro L m i σ hL hm hi hσ
  refine ⟨forms L m i σ hL hm hi hσ, hessian L m i σ hL hm hi hσ, ?_⟩
  intro K k hk hiK Γ hΓ
  exact ⟨sides L m i σ hL hm hi hσ K k hk hiK Γ hΓ,
    fun V hV hV' => operations L m i σ hL hm hi hσ K k hk hiK Γ hΓ V hV hV',
    fun hT V => translation L m i σ hL hm hi hσ hT K k hk hiK Γ hΓ V⟩
end YangMills.Construction.PeriodicLattice
