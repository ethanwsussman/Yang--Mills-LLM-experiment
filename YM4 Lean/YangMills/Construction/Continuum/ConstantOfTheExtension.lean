import YangMills.Construction.Continuum.LocalFunctionalsOfAForm
import YangMills.Construction.Continuum.SystemsOfThePiecesAndTheLeibnizAndTaylorNumbers
import Mathlib
set_option autoImplicit false
noncomputable section
namespace YangMills.Construction.ExtensionConstants
def extConst (n a : ℕ) : ℝ :=
  2 ^ (a + 2) * (ConfigSpace.localConst / PieceScales.sideConstant) ^ n *
    PieceSystems.leibnizConst n * PieceSystems.taylorConst n * ShellPieces.countConst n
def whitneyConst : ℝ :=
  max 48 (max (2 * Bumps.normalizerBound ^ 4) (max ShellPieces.derivConst
    (max ShellPieces.diagDistConst (1024 * Real.exp 2 * ShellPieces.volumeCountConst))))
def factorialConst : ℝ :=
  max (2 * Real.exp 34 * PieceSystems.weightConst ^ 5) (max whitneyConst
    (2 ^ 7 * 36 * 5 ^ 10 * Real.exp 15 * (2 * Bumps.normalizerBound ^ 4) *
      ShellPieces.derivConst ^ 6))
def extFactor : ℝ := 4
def extBase : ℝ := ConfigSpace.localConst * factorialConst ^ 3 / PieceScales.sideConstant
end YangMills.Construction.ExtensionConstants
end
