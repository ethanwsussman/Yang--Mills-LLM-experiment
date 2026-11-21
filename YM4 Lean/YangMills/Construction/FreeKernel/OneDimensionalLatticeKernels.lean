import Mathlib
set_option autoImplicit false
noncomputable section
namespace YangMills.Construction.LatticeKernel
open Complex
def laplacianSymbol (θ : ℝ) : ℝ :=
  2 - 2 * Real.cos θ
def discreteHeatKernel (t : ℝ) (m : ℤ) : ℂ :=
  (1 / (2 * (Real.pi : ℂ))) *
    ∫ θ in (-Real.pi)..Real.pi,
      Complex.exp (I * (m : ℂ) * (θ : ℂ)) * (Real.exp (-t * laplacianSymbol θ) : ℂ)
def gaussianHeatKernel (t ξ : ℝ) : ℝ :=
  Real.exp (-ξ ^ 2 / (4 * t)) / Real.sqrt (4 * Real.pi * t)
def gaussianHeatKernelDeriv (k : ℕ) (t ξ : ℝ) : ℝ :=
  iteratedDeriv k (gaussianHeatKernel t) ξ
def fwdDiff (f : ℤ → ℂ) (m : ℤ) : ℂ :=
  f (m + 1) - f m
def bwdDiff (f : ℤ → ℂ) (m : ℤ) : ℂ :=
  f m - f (m - 1)
inductive DiffKind
  | identity
  | forward
  | backward
  | laplacian
  deriving DecidableEq
def diffOp : DiffKind → (ℤ → ℂ) → ℤ → ℂ
  | .identity, f => f
  | .forward, f => fwdDiff f
  | .backward, f => bwdDiff f
  | .laplacian, f => fwdDiff (bwdDiff f)
def diffOrder : DiffKind → ℕ
  | .identity => 0
  | .forward => 1
  | .backward => 1
  | .laplacian => 2
def diffMultiplier : DiffKind → ℝ → ℂ
  | .identity, _ => 1
  | .forward, θ => Complex.exp (I * (θ : ℂ)) - 1
  | .backward, θ => 1 - Complex.exp (-(I * (θ : ℂ)))
  | .laplacian, θ => -(laplacianSymbol θ : ℂ)
def symbolError (θ : ℝ) : ℝ :=
  laplacianSymbol θ - θ ^ 2
def homotopySymbol (s θ : ℝ) : ℝ :=
  θ ^ 2 + s * symbolError θ
def multiplierError (a : DiffKind) (θ : ℝ) : ℂ :=
  diffMultiplier a θ - (I * (θ : ℂ)) ^ diffOrder a
end YangMills.Construction.LatticeKernel
