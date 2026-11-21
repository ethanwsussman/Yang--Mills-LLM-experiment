import YangMills.Construction.Conventions.StandingParameters
import Mathlib
set_option autoImplicit false
open MeasureTheory Set
noncomputable section
namespace YangMills.Construction
abbrev Conventions.StandingParameters.LatticeIndex (s : Conventions.StandingParameters) : Type :=
  {n : ℕ // n ≤ (s.K : ℕ)}
namespace PeriodicLattice
def levelRange (K n : ℕ) : Finset ℕ := Finset.Icc (K - n) K
end PeriodicLattice
end YangMills.Construction
end
