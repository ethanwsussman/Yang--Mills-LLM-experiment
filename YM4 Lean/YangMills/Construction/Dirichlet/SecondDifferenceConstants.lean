import YangMills.Construction.Dirichlet.BumpDerivativeBounds
import YangMills.Construction.Dirichlet.LocalFormConst
import YangMills.Construction.FreeKernel.HolderFieldInteriorConstants
import Mathlib
set_option autoImplicit false
noncomputable section
namespace YangMills.Construction.Dirichlet.SecondDifference
open FreeKernel
def secondDiffConst (d L : ℕ) (aMinus aPlus : ℝ) : ℝ :=
  Real.exp (5 / 3) +
    (2 * Real.sqrt d + aPlus * (L : ℝ) ^ 2 + (d : ℝ) * bumpSecondDerivSup +
        Real.sqrt d * bumpDerivSup) *
      (L : ℝ) * localFormConst L aMinus
def cappedExponent (ε β₀ : ℝ) : ℝ := min ε ((1 - β₀) / 2)
def uniformConst (d L : ℕ) (aMinus : ℝ) : ℝ :=
  Real.sqrt ((d : ℝ) * (5 : ℝ) ^ d) * (L : ℝ) ^ ((d : ℝ) / 2) * localFormConst L aMinus
def normConst (d L : ℕ) (aMinus aPlus : ℝ) : ℝ :=
  (1 + 64 * aPlus * (L : ℝ) ^ (2 + (d : ℝ) / 2)) * uniformConst d L aMinus +
    136 * expOne * (L : ℝ) ^ 2
def pointwiseConst (d L : ℕ) (aMinus aPlus ε β₀ : ℝ) : ℝ :=
  max (4 * uniformConst d L aMinus)
    (1 / 8 * holderFieldInteriorConst d (cappedExponent ε β₀) β₀ * normConst d L aMinus aPlus)
def pointwiseBoundConst (d L : ℕ) (aMinus aPlus ε : ℝ) : ℝ := pointwiseConst d L aMinus aPlus ε 0
def holderBoundConst (d L : ℕ) (aMinus aPlus ε β₀ : ℝ) : ℝ :=
  5 * pointwiseConst d L aMinus aPlus ε β₀
end YangMills.Construction.Dirichlet.SecondDifference
