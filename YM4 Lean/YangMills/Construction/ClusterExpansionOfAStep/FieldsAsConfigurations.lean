import YangMills.Construction.ClusterExpansionOfAStep.UnitQuaternionsAsSpecialUnitaryMatrices
import YangMills.Construction.Lattice.SiteCoordinates
import Mathlib
set_option autoImplicit false
noncomputable section
namespace YangMills.Construction.ClusterExpansionOfAStep
open SoftAverages
variable {n : ℕ}
def periodicLatticeSite (L m : ℕ) (j : ℤ) (x : TorusFields.TorusSite n) : PeriodicLattice.Site L m j :=
  PeriodicLattice.offsetSite 0 fun μ => ((x μ).cast : ℤ)
def torusSiteOfLatticeSite (n : ℕ) {L m : ℕ} {j : ℤ} (s : PeriodicLattice.Site L m j) : TorusFields.TorusSite n :=
  fun μ => ((s.2.choose μ : ℤ) : ZMod n)
def fieldOnPositiveBond {L m : ℕ} {j : ℤ} (W : TorusFields.TorusField n)
    (b : PeriodicLattice.PositivelyOrientedBond L m j) : Matrices.ComplexMatrix2.specialUnitary :=
  unitQuaternionEquivSpecialUnitary (W (torusSiteOfLatticeSite n b.1.source) b.1.axis)
def gaugeFieldOfTorusField (L m : ℕ) (j : ℤ) (W : TorusFields.TorusField n) :
    PeriodicLattice.Bond L m j → Matrices.ComplexMatrix2 :=
  PeriodicLattice.gaugeFieldOfPositive (fieldOnPositiveBond W)
end YangMills.Construction.ClusterExpansionOfAStep
end
