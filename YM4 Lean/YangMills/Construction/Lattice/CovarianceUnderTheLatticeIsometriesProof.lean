import YangMills.Construction.Lattice.CovarianceUnderTheLatticeIsometries
import Mathlib
namespace YangMills.Construction.PeriodicLattice
theorem latticeIsometryCovariance_of_parts
    (hGroup : LatticeIsometryGroupActionStatement)
    (hBlocks : IsometryInvariance.InvariantUnderIsometries)
    (hTowers : IsometriesPreserveTowersAndStepCubes)
    (hHol : IsometryCovariance.Statement)
    (hAvg : AveragingMapsEquivariant)
    (hFix : GaugeFixingCovarianceStatement)
    (hOrb : IsometryCovarianceOfMinimalOrbits)
    (hAxial : IsometryCovariantRegularSetsAndAxialGauge)
    (hTwist : TwistedTransportIsometryInvariance)
    (hStep : IsometryCovarianceOneStep)
    (hCHol : ComplexHolonomiesAndAveragesCovariance.Statement)
    (hCGauge : ComplexGaugeAndMinimalFieldCovariance.Statement)
    (hCForms : ComplexFormsAndStepOperationsCovariance.Statement) :
    LatticeIsometryCovariance :=
  ⟨hGroup, hBlocks, hTowers, hHol, hAvg, hFix, hOrb, hAxial, hTwist, hStep, hCHol, hCGauge, hCForms⟩
end YangMills.Construction.PeriodicLattice
