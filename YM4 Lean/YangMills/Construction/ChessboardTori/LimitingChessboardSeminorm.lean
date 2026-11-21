import YangMills.Construction.ChessboardTori.ChessboardEstimate
import Mathlib
set_option autoImplicit false
open Filter
noncomputable section
namespace YangMills.Construction
namespace ChessboardTori
namespace ReflectionGrid
variable {D : ChessboardSetup} (g : ReflectionGrid D)
def normAtExponent (m' : ℕ+) (S : Set YangMills.Construction.InfiniteLattice.AmbientSpace)
    (F : D.GaugeField → ℂ) : ℝ :=
  (g.withExponent m').chessboardNorm S F
def limChessboardNorm (F : D.GaugeField → ℂ) : ℝ :=
  limsup (fun m' : ℕ+ => g.normAtExponent m' (g.cell 0) F) atTop
end ReflectionGrid
end ChessboardTori
end YangMills.Construction
end
