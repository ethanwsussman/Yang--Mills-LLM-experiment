import YangMills.Construction.BackgroundField.NumbersOfTheMinimalOrbitsTheorem
import YangMills.Construction.Lattice.CriticalConfigurationsOverABlockField
import YangMills.Construction.Lattice.FourNumbersThatBoundThePropagators
import Mathlib
set_option autoImplicit false
noncomputable section
namespace YangMills.Construction
open PeriodicLattice
namespace BackgroundField.GapBlockProductFloor
open PrescribedAverageProblem
structure AboveThresholds (L : ℕ) (r : ℝ) : Prop where
  orbit_le : subcriticalProductFloor L ≤ r
  critical_le : (criticalMinPower L : ℝ) ≤ r
  propagator_le : (PropagatorConstants.radius L : ℝ) ≤ r
end BackgroundField.GapBlockProductFloor
end YangMills.Construction
end
