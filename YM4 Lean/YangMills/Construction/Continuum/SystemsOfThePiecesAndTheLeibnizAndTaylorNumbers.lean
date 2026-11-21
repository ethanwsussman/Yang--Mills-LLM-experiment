import YangMills.Construction.Continuum.PiecesOfTheShellsTheirCubesAndNumbers
import Mathlib
set_option autoImplicit false
noncomputable section
namespace YangMills.Construction.PieceSystems
open Bumps ConfigSpace PieceScales ShellPieces
variable {n : ℕ}
def centreAndSide (p : activeIndices n) : Config n × ℝ := (pieceCentre p.1.1 p.1.2, pieceSide p.1.1)
def weightConst : ℝ := 10
def leibnizConst (n : ℕ) : ℝ := 2 ^ (5 * n + 1) * derivBound n (5 * n + 1)
theorem leibnizConst_eq (n : ℕ) :
    leibnizConst n = 2 ^ (5 * n + 1) * (2 * normalizerBound ^ (4 * n) *
      (derivConst * n) ^ (5 * n + 1) * ((5 * n + 1).factorial : ℝ) ^ 2) := rfl
def taylorConst (n : ℕ) : ℝ :=
  Real.exp (32 * n) * (weightConst * Real.sqrt n) ^ (4 * n + 2)
end YangMills.Construction.PieceSystems
end
