import YangMills.Construction.ChessboardTori.FromTheInfiniteLatticeToTheTorus
import YangMills.Construction.InfiniteLattice.ChessboardObjectsOfAMirrorGrid
import YangMills.Construction.InfiniteLattice.EvaluationsOnTheCopiesOfAMirrorGrid
import Mathlib
set_option autoImplicit false
namespace YangMills.Construction.MultipleReflections
theorem liftsCommuteHolds
    (hObjects : ChessboardObjectsHold)
    (hTorus : ChessboardTori.TorusReduction.Statement) :
    LiftsCommuteHolds := by
  intro D G h k k' F hF
  obtain ⟨-, -, -, -, -, hcell, -, halg, hcopy⟩ := hObjects D G
  obtain ⟨hA, hB, -⟩ :=
    hTorus D.toChessboardSetup G.toChessboardGrid (G.two_mul_cellSide_le_torusSide h)
  have hcells : ∀ j, G.toChessboardGrid.cell j ∈ G.toChessboardGrid.cellSet := fun j => ⟨j, rfl⟩
  have hF' : F ∈ ChessboardTori.ReflectionGrid.cellObservables (D := D.toChessboardSetup)
      (G.toChessboardGrid.cell k) := by
    rw [halg]
    exact hF
  refine ⟨?_, fun U => ?_⟩
  · have hread := (hA _ (hcells k)).2.1 F hF'
    rw [hcell k] at hread
    exact hread
  · have hsame := hB _ (hcells k) _ (hcells k') F hF' U.1 U.2
    rw [hcopy k k' F hF, hcell k, hcell k'] at hsame
    exact hsame
end YangMills.Construction.MultipleReflections
