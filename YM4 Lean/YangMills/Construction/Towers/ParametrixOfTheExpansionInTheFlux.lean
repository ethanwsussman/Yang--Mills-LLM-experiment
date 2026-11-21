import YangMills.Construction.Towers.TheMassiveFunctional
import Mathlib
set_option autoImplicit false
noncomputable section
namespace YangMills.Construction
open PeriodicOperators (toComplexVec)
open InfiniteLattice (AmbientSpace)
namespace Tower.MagneticWeyl.FluxExpansion
def baseSymbol (q : AmbientSpace) : ℂ := Massive.latticeSymbol (toComplexVec q)
def baseSymbolDeriv (μ : Fin 4) (q : AmbientSpace) : ℂ := 2 * Complex.sin (q μ)
def baseSymbolSecondDeriv (μ : Fin 4) (q : AmbientSpace) : ℂ := 2 * Complex.cos (q μ)
def shiftedInverse (s : ℝ) (q : AmbientSpace) : ℂ := (baseSymbol q + s)⁻¹
def shiftedInverseSecondDeriv (s : ℝ) (μ : Fin 4) (q : AmbientSpace) : ℂ :=
  -(shiftedInverse s q ^ 2 * baseSymbolSecondDeriv μ q) +
    2 * shiftedInverse s q ^ 3 * baseSymbolDeriv μ q ^ 2
variable {N' : ℕ}
def baseSymbolMatrix (N' : ℕ) (q : AmbientSpace) : Matrix (Fin N') (Fin N') ℂ := baseSymbol q • 1
def termZero (N' : ℕ) (s : ℝ) (q : AmbientSpace) : Matrix (Fin N') (Fin N') ℂ :=
  shiftedInverse s q • 1
def termOne (s : ℝ) (σ₁ : AmbientSpace → Matrix (Fin N') (Fin N') ℂ) (q : AmbientSpace) :
    Matrix (Fin N') (Fin N') ℂ :=
  (-(shiftedInverse s q ^ 2)) • σ₁ q
def termTwo (s : ℝ) (σ₁ σ₂ : AmbientSpace → Matrix (Fin N') (Fin N') ℂ) (q : AmbientSpace) :
    Matrix (Fin N') (Fin N') ℂ :=
  shiftedInverse s q • (shiftedInverse s q ^ 2 • σ₁ q ^ 2 - shiftedInverse s q • σ₂ q +
    ((1 / 8 : ℂ) * (shiftedInverseSecondDeriv s 0 q * baseSymbolSecondDeriv 1 q +
      shiftedInverseSecondDeriv s 1 q * baseSymbolSecondDeriv 0 q)) •
      (1 : Matrix (Fin N') (Fin N') ℂ))
def approxInverse (s φ : ℝ) (σ₁ σ₂ : AmbientSpace → Matrix (Fin N') (Fin N') ℂ) (q : AmbientSpace) :
    Matrix (Fin N') (Fin N') ℂ :=
  termZero N' s q + (φ : ℂ) • termOne s σ₁ q + (φ : ℂ) ^ 2 • termTwo s σ₁ σ₂ q
end Tower.MagneticWeyl.FluxExpansion
end YangMills.Construction
end
