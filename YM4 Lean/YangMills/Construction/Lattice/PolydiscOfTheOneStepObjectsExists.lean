import YangMills.Construction.Conventions.StandingParameters
import YangMills.Construction.Lattice.PolydiscOfTheOneStepObjects
import Mathlib
noncomputable section
namespace YangMills.Construction.PeriodicLattice
def ExistsOneStepPolydiscRadius : Prop :=
  ∀ L : ℕ, Conventions.IsAdmissibleBlockingFactor L → ∃ r : ℝ, IsAdmissiblePolydiscRadius L r
end YangMills.Construction.PeriodicLattice
end
