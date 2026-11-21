import YangMills.Construction.Conventions.StandingParameters
import YangMills.Construction.Lattice.IsometryGroupsOfTheTorus
import Mathlib
set_option autoImplicit false
noncomputable section
namespace YangMills.Construction
namespace Conventions.StandingParameters
def affineTorusMaps (p : StandingParameters) (i : ℤ) (_hi : -(p.m : ℤ) ≤ i) :
    Set (p.Torus ≃ p.Torus) :=
  PeriodicLattice.latticeIsometries p.L p.m i
end Conventions.StandingParameters
end YangMills.Construction
