import YangMills.Construction.Lattice.ConstraintSetsAndAxialGaugeAtComplexConfigurationsUnderIsometries
import YangMills.Construction.Lattice.ContinuationOfTheMinimiserUnderIsometries
import YangMills.Construction.Lattice.CovarianceOfComplexGaugeAndMinimalConfigurations
import YangMills.Construction.Lattice.GaugeActionsAtComplexConfigurationsUnderIsometries
import YangMills.Construction.Lattice.TowerConfigurationsOfTheContinuationUnderIsometries
import Mathlib
set_option autoImplicit false
namespace YangMills.Construction.PeriodicLattice
theorem complexGaugeAndMinimalFieldCovariance_holds
    (h1 : ComplexGaugeCovarianceUnderIsometries.Statement)
    (h2 : IsometriesPreserveComplexConstraintSetsAndAxialGauge)
    (h3 : IsometriesPreserveMinimizerContinuation)
    (h4 : continuedTowerField_isometry_statement) :
    ComplexGaugeAndMinimalFieldCovariance.Statement := by
  intro L m hL hm i hi σ hσ
  obtain ⟨a1, a2⟩ := h1 L m hL hm i hi σ hσ
  obtain ⟨b1, b2⟩ := h2 L m hL hm i hi σ hσ
  exact ⟨a1, fun K k Ω hΩ => ⟨(a2 K k Ω hΩ).1, (a2 K k Ω hΩ).2, b1 K k Ω hΩ⟩, b2,
    h3 L m hL hm i hi σ hσ, h4 L m hL hm i hi σ hσ⟩
end YangMills.Construction.PeriodicLattice
