import YangMills.Construction.ChessboardTori.BoxWithAnOuterConfiguration
import Mathlib
set_option autoImplicit false
noncomputable section
namespace YangMills.Construction.ChessboardTori
def ZeroSourcePartition.Statement : Prop :=
  ∀ D : ChessboardSetup, D.partitionFunction 0 = D.torusPartition (fun _ => 1)
end YangMills.Construction.ChessboardTori
end
