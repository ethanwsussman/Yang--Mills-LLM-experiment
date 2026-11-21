import YangMills.Construction.ChessboardTori.NamesOfAMirrorGridOnATorus
import Mathlib
set_option autoImplicit false
noncomputable section
namespace YangMills.Construction.ChessboardTori.ReflectionGrid
variable {D : ChessboardSetup} (g : ReflectionGrid D)
def torusChessboardNormAtSide (_hside : 2 * g.cellSide ≤ PeriodicLattice.torusSide D.L D.m)
    {C : Set D.Torus} (_hC : C ∈ g.torusCellSet) (F : (D.PeriodicLink → Matrices.ComplexMatrix2) → ℂ)
    (_hF : F ∈ g.torusCellObservables C) : ℝ :=
  g.torusChessboardNorm F
theorem torusChessboardNormAtSide_eq (hside : 2 * g.cellSide ≤ PeriodicLattice.torusSide D.L D.m)
    {C : Set D.Torus} (hC : C ∈ g.torusCellSet) (F : (D.PeriodicLink → Matrices.ComplexMatrix2) → ℂ)
    (hF : F ∈ g.torusCellObservables C) :
    g.torusChessboardNormAtSide hside hC F hF =
      ‖D.periodicExpectation (g.torusProduct F)‖ ^ (1 / g.cellsAcross ^ 4) :=
  rfl
end YangMills.Construction.ChessboardTori.ReflectionGrid
end
