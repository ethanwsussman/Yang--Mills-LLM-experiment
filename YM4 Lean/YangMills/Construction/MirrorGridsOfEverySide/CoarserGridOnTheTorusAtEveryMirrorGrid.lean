import YangMills.Construction.MirrorGridsOfEverySide.PropertiesOfAMirrorGrid
import Mathlib
set_option autoImplicit false
noncomputable section
namespace YangMills.Construction
open ChessboardTori (ReflectionGrid)
namespace MirrorGridsAllSides
def AllGridsCoarseningOnTorus : Prop :=
  ∀ (D : GridSetup) (g : ReflectionGrid D), g.HasAdmissibleSide →
    ∀ (h : ReflectionGrid D) (n : ℕ), h.IsCoarsening g → h.cellSide = (D.L : ℝ) ^ n * g.cellSide →
      2 * h.cellSide ≤ PeriodicLattice.torusSide D.L D.m → CoarseningOnTorus g h n
end MirrorGridsAllSides
end YangMills.Construction
end
