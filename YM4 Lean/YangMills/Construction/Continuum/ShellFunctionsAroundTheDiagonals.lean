import YangMills.Construction.Continuum.DiagonalFlatSchwartz
import YangMills.Construction.RealFunctions.SmoothBumps
import Mathlib
set_option autoImplicit false
noncomputable section
namespace YangMills.Construction
namespace DiagonalShells
open Bumps ConfigSpace
def pairCutoff (j : ℕ) (y : Fin 4 → ℝ) : ℝ :=
  1 - ∏ c : Fin 4, (1 - symmetricTransition (2 ^ j * y c))
def tupleCutoff {n : ℕ} (j : ℕ) (x : Config n) : ℝ :=
  ∏ p ∈ Finset.univ.filter (fun p : Fin n × Fin n => p.1 < p.2),
    pairCutoff j (x p.1 - x p.2)
def shellLayer {n : ℕ} : ℕ → Config n → ℝ
  | 0 => tupleCutoff 0
  | j + 1 => tupleCutoff (j + 1) - tupleCutoff j
def tupleCutoffConst : ℝ := twiceGevreyConst * normalizerBound ^ 4
end DiagonalShells
end YangMills.Construction
