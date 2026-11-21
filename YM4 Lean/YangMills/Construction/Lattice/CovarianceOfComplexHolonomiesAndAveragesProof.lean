import YangMills.Construction.Lattice.CovarianceOfComplexActions
import YangMills.Construction.Lattice.CovarianceOfComplexAverages
import YangMills.Construction.Lattice.CovarianceOfComplexAveragingOfDeterminingSets
import YangMills.Construction.Lattice.CovarianceOfComplexContourVariables
import YangMills.Construction.Lattice.CovarianceOfComplexHolonomies
import YangMills.Construction.Lattice.CovarianceOfComplexHolonomiesAndAverages
import YangMills.Construction.Lattice.CovarianceOfComplexLifts
import YangMills.Construction.Lattice.CovarianceOfComplexPlaquetteVariables
import YangMills.Construction.Lattice.CovarianceOfLinearisedAveragesOfComplexForms
import Mathlib
set_option autoImplicit false
namespace YangMills.Construction.PeriodicLattice
theorem complexHolonomiesAndAveragesCovariance_holds
    (h1 : ComplexHolonomyCovariance)
    (h2 : PlaquetteVariablesCovarianceStatement)
    (h3 : ComplexEnergiesIsometryInvariant)
    (h4 : ComplexContourHolonomyCovariance)
    (h5 : ComplexAveragesCommuteWithIsometries.Statement)
    (h6 : ComplexLevelLiftsEquivariant)
    (h7 : ComplexDeterminingAveragingCovariance.Statement)
    (h8 : LinearBlockIteratesEquivariant) :
    ComplexHolonomiesAndAveragesCovariance.Statement := by
  obtain ⟨ε, h2⟩ := h2
  exact ⟨ε, fun L m i σ hL hm hi hσ =>
    ⟨h1 L m i σ hL hm hi hσ, h2 L m i σ hL hm hi hσ, h3 L m i σ hL hm hi hσ,
      h4 L m i σ hL hm hi hσ, h5 L m i σ hL hm hi hσ, h6 L m i σ hL hm hi hσ,
      h7 L m i σ hL hm hi hσ, h8 L m i σ hL hm hi hσ⟩⟩
end YangMills.Construction.PeriodicLattice
