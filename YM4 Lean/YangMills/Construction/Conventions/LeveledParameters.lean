import YangMills.Construction.Conventions.StandingParameters
import Mathlib
set_option autoImplicit false
noncomputable section
namespace YangMills.Construction.Conventions
structure LeveledParameters extends StandingParameters where
  t : ℕ
  t_le_cutoff : t ≤ (K : ℕ)
namespace LeveledParameters
variable (s : LeveledParameters)
def toLevelUnits (r : ℝ) : ℝ := YangMills.Construction.PeriodicLattice.toLevelUnits s.L s.K s.t r
def finestMesh : ℝ := YangMills.Construction.PeriodicLattice.finestMeshInLevelUnits s.L s.t
def coarseMesh (n : ℕ) : ℝ := (s.L : ℝ) ^ ((n : ℤ) - (s.t : ℤ))
end LeveledParameters
end YangMills.Construction.Conventions
end
