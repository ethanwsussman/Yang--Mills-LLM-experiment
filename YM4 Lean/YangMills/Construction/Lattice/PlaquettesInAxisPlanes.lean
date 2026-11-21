import YangMills.Construction.Lattice.ContinuumCurvatureKernel
import Mathlib
set_option autoImplicit false
noncomputable section
namespace YangMills.Construction.PeriodicLattice
variable {L m : ℕ} {j : ℤ}
def Plaquette.axisPlane (p : Plaquette L m j) : AxisPlane :=
  ⟨p.firstAxis, p.secondAxis, p.firstAxis_lt_secondAxis⟩
def planeCenterOffset (P : AxisPlane) : Fin 4 → ℝ :=
  (1 / 2 : ℝ) • (Pi.single P.lower 1 + Pi.single P.upper 1)
end YangMills.Construction.PeriodicLattice
end
