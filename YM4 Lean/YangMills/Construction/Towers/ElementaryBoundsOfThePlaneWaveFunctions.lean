import YangMills.Construction.Towers.OddReciprocalWeightsAndTheirSum
import YangMills.Construction.Towers.PlaneWaves
import Mathlib
set_option autoImplicit false
open scoped ENNReal
noncomputable section
namespace YangMills.Construction
namespace Tower
namespace PlaneWaves
namespace PlaneWaveBounds
open YangMills.Construction.PeriodicOperators (toComplexVec)
def complexPoint (q' θ : Fin 4 → ℝ) : Fin 4 → ℂ :=
  fun ν => (q' ν : ℂ) + Complex.I * (θ ν : ℂ)
def realSymbolSquare (L k : ℕ) (q' : Fin 4 → ℝ) : ℝ :=
  ∑ ν, ‖forwardSymbol L k (toComplexVec q') ν‖ ^ 2
def SymbolBounds (L k : ℕ) (q' θ : Fin 4 → ℝ) : Prop :=
  (∀ ν, 2 / Real.pi * |q' ν| ≤ ‖forwardSymbol L k (toComplexVec q') ν‖ ∧
    ‖forwardSymbol L k (toComplexVec q') ν‖ ≤ |q' ν|) ∧
  9 / 10 * (realSymbolSquare L k q' + 1) ≤ (symbolSquare L k (complexPoint q' θ) + 1).re ∧
  (symbolSquare L k (complexPoint q' θ) + 1).re ≤ ‖symbolSquare L k (complexPoint q' θ) + 1‖ ∧
  ‖symbolSquare L k (complexPoint q' θ) + 1‖ ≤ 3 * (realSymbolSquare L k q' + 1) ∧
  (∀ ν, ‖forwardSymbol L k (complexPoint q' θ) ν‖ ≤
      6 / 5 * (‖forwardSymbol L k (toComplexVec q') ν‖ + 1 / 8) ∧
    ‖forwardSymbol L k (-complexPoint q' θ) ν‖ ≤
      6 / 5 * (‖forwardSymbol L k (toComplexVec q') ν‖ + 1 / 8)) ∧
  (4 ≤ realSymbolSquare L k q' →
    1 / 2 * realSymbolSquare L k q' ≤ ‖symbolSquare L k (complexPoint q' θ)‖)
def DirichletSumBounds (L k : ℕ) (q' θ : Fin 4 → ℝ) : Prop :=
  ∀ ν,
    ‖dirichletSum L k (complexPoint q' θ ν)‖ ≤ Real.exp (1 / 16) ∧
    (|q' ν| ≤ Real.pi → θ ν = 0 →
      (dirichletSum L k (complexPoint q' θ ν)).im = 0 ∧
      2 / Real.pi ≤ (dirichletSum L k (complexPoint q' θ ν)).re ∧
      1 - (dirichletSum L k (complexPoint q' θ ν)).re ^ 2 ≤ 1 / 12 * q' ν ^ 2) ∧
    ∀ (p : ℂ) (m : ℤ), complexPoint q' θ ν = p + 2 * (Real.pi : ℂ) * (m : ℂ) →
      |p.re| ≤ Real.pi → m ≠ 0 →
      ‖dirichletSum L k (complexPoint q' θ ν)‖ ≤ ‖Complex.sin (p / 2)‖ * (2 * |(m : ℝ)| - 1)⁻¹ ∧
      ‖Complex.sin (p / 2)‖ * (2 * |(m : ℝ)| - 1)⁻¹ ≤ 2 * (2 * |(m : ℝ)| - 1)⁻¹
def Claim : Prop :=
  (∀ L k : ℕ, Conventions.IsAdmissibleBlockingFactor L → 1 ≤ k → ∀ q' θ : Fin 4 → ℝ,
    (∀ ν, |q' ν| ≤ Real.pi / finestMesh L k) → (∀ ν, |θ ν| ≤ 1 / 8) →
      symbolSquare L k (toComplexVec q') = (realSymbolSquare L k q' : ℂ) ∧
      SymbolBounds L k q' θ ∧ DirichletSumBounds L k q' θ) ∧
  oddHarmonicWeightSum < ∞
end PlaneWaveBounds
end PlaneWaves
end Tower
end YangMills.Construction
end
