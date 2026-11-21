import Mathlib
set_option autoImplicit false
noncomputable section
namespace YangMills.Construction.PeriodicLattice.WidthRateFloor
def islandHullMultiplicity : ℕ := 4 ^ 4 + 27 ^ 4
def domainSumRateFloor : ℝ := max 33 ((23 + (islandHullMultiplicity : ℝ)) * Real.log 2)
end YangMills.Construction.PeriodicLattice.WidthRateFloor
end
