import YangMills.Construction.Conventions.StandingParameters
import Mathlib
set_option autoImplicit false
noncomputable section
namespace YangMills.Construction.SeparatedSequences
structure LevelScaledParameters extends Conventions.StandingParameters where
  level : ℕ
  level_le_K : level ≤ (K : ℕ)
namespace LevelScaledParameters
variable (P : LevelScaledParameters)
def baseMesh : ℝ := PeriodicLattice.finestMeshInLevelUnits P.L P.level
end LevelScaledParameters
end YangMills.Construction.SeparatedSequences
end
