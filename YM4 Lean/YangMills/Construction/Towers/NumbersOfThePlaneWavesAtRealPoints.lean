import YangMills.Construction.Coercivity.FiniteFamilyBounds
import YangMills.Construction.PeriodicOperators.Jets
import YangMills.Construction.Towers.PlaneWaves
import Mathlib
set_option autoImplicit false
noncomputable section
namespace YangMills.Construction
namespace Tower
namespace RealFrequencyFamily
open PeriodicOperators (realDualPoints)
open PlaneWaves
open Coercivity (IsAdmissibleFamily)
def symbolSquares (L k : ℕ) (κ : Fin 4 → ℂ) (m : Fin 4 → ℤ) : ℝ :=
  (PlaneWaves.symbolSquare L k (PlaneWaves.shiftedFreq κ m)).re
def symbols (L k : ℕ) (κ : Fin 4 → ℂ) (m : Fin 4 → ℤ) : Fin 4 → ℂ :=
  PlaneWaves.forwardSymbol L k (PlaneWaves.shiftedFreq κ m)
def vertexWeights (L k : ℕ) (κ : Fin 4 → ℂ) (m : Fin 4 → ℤ) : ℝ :=
  (PlaneWaves.vertexWeight L k (PlaneWaves.shiftedFreq κ m)).re
def edgeWeights (L k : ℕ) (κ : Fin 4 → ℂ) (m : Fin 4 → ℤ) : Fin 4 → ℂ :=
  PlaneWaves.edgeWeight L k (PlaneWaves.shiftedFreq κ m)
def FamilyBoundsHold : Prop :=
  ∀ L : ℕ, Conventions.IsAdmissibleBlockingFactor L → ∀ k : ℕ, 1 ≤ k → ∀ κ ∈ realDualPoints,
    ∃ z : Fin 4 → ℤ, IsAdmissibleFamily ((2 / Real.pi) ^ 4) ((2 / Real.pi) ^ 5) (4 * Real.pi ^ 2)
      (Real.pi ^ 2 / 48) (PlaneWaves.freqBox L k) z (symbolSquares L k κ) (symbols L k κ)
      (vertexWeights L k κ) (edgeWeights L k κ) (PlaneWaves.unitSymbol κ)
end RealFrequencyFamily
end Tower
end YangMills.Construction
end
