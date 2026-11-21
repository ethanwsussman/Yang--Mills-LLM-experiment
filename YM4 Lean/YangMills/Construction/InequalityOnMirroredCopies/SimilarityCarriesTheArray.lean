import YangMills.Construction.ChessboardTori.SidesCentresAndTheChessboardFunctional
import YangMills.Construction.InequalityOnMirroredCopies.ArrayOnRectangularTori
import Mathlib
set_option autoImplicit false
noncomputable section
namespace YangMills.Construction.ReflectedCopies
open ChessboardTori
def SimilarityPreservesTiledIntegral : Prop :=
  ∀ (D : ChessboardSetup) (g : ReflectionGrid D), g.HasAdmissibleSide → g.q < 0 →
    ∃ (D' : ChessboardSetup) (g' : ReflectionGrid D'), D'.L = D.L ∧ D'.β = D.β ∧ g'.IsCoarse ∧
      g'.HasAdmissibleSide ∧
      (∀ n : EvenIndexVector, torusPartition g n = torusPartition g' n) ∧
      ∀ S ∈ g.cellSet, ∃ S' ∈ g'.cellSet, ∃ Φ : (D.GaugeField → ℂ) → D'.GaugeField → ℂ,
        ∀ F ∈ ReflectionGrid.cellObservables (D := D) S, Φ F ∈ ReflectionGrid.cellObservables (D := D') S' ∧
          ∀ n : EvenIndexVector, tiledIntegral g n S F = tiledIntegral g' n S' (Φ F)
end YangMills.Construction.ReflectedCopies
end
