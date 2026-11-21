import YangMills.Construction.Lattice.PeriodicLattices
import YangMills.Construction.Matrices.SpecialUnitaryTwo
import Mathlib
set_option autoImplicit false
noncomputable section
namespace YangMills.Construction.PeriodicLattice
open YangMills.Construction.Matrices
variable {L m K j : ℕ}
def siteLog (g : SiteAtLevel L m K j → ComplexMatrix2) : SiteAtLevel L m K j → ComplexMatrix2 :=
  fun x => Complex.I⁻¹ • ComplexMatrix2.logSeries (g x)
end YangMills.Construction.PeriodicLattice
