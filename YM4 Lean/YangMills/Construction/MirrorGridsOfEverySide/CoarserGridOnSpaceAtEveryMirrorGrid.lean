import YangMills.Construction.MirrorGridsOfEverySide.PropertiesOfAMirrorGrid
import Mathlib
set_option autoImplicit false
noncomputable section
namespace YangMills.Construction
open ChessboardTori (ReflectionGrid)
namespace MirrorGridsAllSides
def AllGridsCoarseningOnSpace : Prop :=
  ∀ (D : GridSetup) (g : ReflectionGrid D), g.HasAdmissibleSide →
    ∀ (h : ReflectionGrid D) (n : ℕ), h.IsCoarsening g → h.cellSide = (D.L : ℝ) ^ n * g.cellSide →
      CoarseningOnSpace g h n
end MirrorGridsAllSides
end YangMills.Construction
end
