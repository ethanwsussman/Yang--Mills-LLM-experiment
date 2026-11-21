import YangMills.Construction.Lattice.ObservablesAndTestNorms
import Mathlib
set_option autoImplicit false
noncomputable section
namespace YangMills.Construction.TrajectoryData
def tentProfile (r : ℝ) : ℝ := max (min 1 (2 * (1 - r))) 0
def torusPointOf (L m : ℕ) (v : Fin 4 → ℝ) : PeriodicLattice.FourTorus L m :=
  TorusMetric.torusProj (PeriodicLattice.torusSide L m) v
def firstBump (L m : ℕ) (n : ℝ) (v : Fin 4 → ℤ) : PeriodicLattice.FourTorus L m → ℝ := fun p =>
  tentProfile (TestFunctions.euclidDistTorus (ℓ := PeriodicLattice.torusSide L m) p
    (torusPointOf L m fun i => (v i : ℝ)) / (0.99 * n))
def translatedBump (L m : ℕ) (n : ℝ) (v : Fin 4 → ℤ) : PeriodicLattice.FourTorus L m → ℝ := fun p =>
  firstBump L m n v (p - torusPointOf L m (Pi.single 0 (3.5 * n)))
end YangMills.Construction.TrajectoryData
end
