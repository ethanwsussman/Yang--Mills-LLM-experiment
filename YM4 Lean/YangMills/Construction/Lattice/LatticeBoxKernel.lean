import YangMills.Construction.Lattice.BackgroundCurvatureAndTheThreeCovariances
import YangMills.Construction.Lattice.RingsAndRingKernels
import Mathlib
noncomputable section
namespace YangMills.Construction.PeriodicLattice
variable (S : Conventions.StandingParameters)
theorem isSymmetricKernel_backgroundCurvatureCovariance (s : ℕ) :
    IsSymmetricKernel (backgroundCurvatureCovariance S s) := by apply _root_.YangMills.Construction.PeriodicLattice.backgroundCurvatureCovariance_comm <;> assumption
def boxKernel (s : ℕ) (φ : Fin 4 → Plaquette S.L S.m ((S.K : ℕ) : ℤ) → ℝ) : ℝ :=
  cyclicKernel (backgroundCurvatureCovariance S s) φ
end YangMills.Construction.PeriodicLattice
