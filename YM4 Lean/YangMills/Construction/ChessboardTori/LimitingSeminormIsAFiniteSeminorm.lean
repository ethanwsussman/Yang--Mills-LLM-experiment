import YangMills.Construction.ChessboardTori.LimitingChessboardSeminorm
import Mathlib
set_option autoImplicit false
open Filter
noncomputable section
namespace YangMills.Construction.ChessboardTori
def LimChessboardNormIsSeminorm.Statement : Prop :=
  ∀ (D : ChessboardSetup) (g : ReflectionGrid D), g.IsCoarse →
    (∀ F ∈ ReflectionGrid.cellObservables (D := D) (g.cell 0),
      IsBoundedUnder (· ≤ ·) atTop (fun n : ℕ+ => g.normAtExponent n (g.cell 0) F) ∧
      IsBoundedUnder (· ≥ ·) atTop (fun n : ℕ+ => g.normAtExponent n (g.cell 0) F) ∧
      0 ≤ g.limChessboardNorm F ∧
      (∀ c : ℂ, g.limChessboardNorm (c • F) = ‖c‖ * g.limChessboardNorm F) ∧
      (∀ G ∈ ReflectionGrid.cellObservables (D := D) (g.cell 0),
        g.limChessboardNorm (F + G) ≤ g.limChessboardNorm F + g.limChessboardNorm G) ∧
      g.limChessboardNorm (fun U => starRingEnd ℂ (F U)) = g.limChessboardNorm F ∧
      g.limChessboardNorm F ≤ InfiniteLattice.observableSupNorm F) ∧
    g.limChessboardNorm (fun _ => 1) = 1
end YangMills.Construction.ChessboardTori
end
