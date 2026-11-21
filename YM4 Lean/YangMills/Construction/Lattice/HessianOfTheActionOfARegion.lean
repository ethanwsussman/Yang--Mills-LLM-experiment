import YangMills.Construction.Lattice.LieValuedBondFunctions
import YangMills.Construction.Lattice.WeightedWilsonActions
import Mathlib
set_option autoImplicit false
noncomputable section
namespace YangMills.Construction.PeriodicLattice
variable {L m K : ℕ}
def regionEnergyHessian (k : ℕ) (Ω : Set (FourTorus L m))
    (U A B : BondAtLevel L m K 0 → Matrices.ComplexMatrix2) : ℂ :=
  deriv (fun s : ℝ => deriv (fun t : ℝ =>
    interiorEnergy Ω (bareTwist k ((s : ℂ) • A + (t : ℂ) • B) U)) 0) 0
end YangMills.Construction.PeriodicLattice
