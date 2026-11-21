import YangMills.Construction.ChessboardTori.GridsCellsAndCopies
import Mathlib
set_option autoImplicit false
open Set
noncomputable section
namespace YangMills.Construction.ChessboardTori
open InfiniteLattice (AmbientSpace)
namespace ChessboardSetup
variable (D : ChessboardSetup)
def unitReflectionGrid : ReflectionGrid D where
  q := 0
  one_sub_K_le_q := by
    have := D.K.pos
    omega
  origin _ := D.mesh / 2
  origin_mem _ := ⟨0, by push_cast; ring⟩
theorem unitReflectionGrid_isCoarse : D.unitReflectionGrid.IsCoarse := le_rfl
def unitReflectionGroup : Subgroup (Equiv.Perm AmbientSpace) := D.unitReflectionGrid.reflectionGroup
end ChessboardSetup
end YangMills.Construction.ChessboardTori
end
