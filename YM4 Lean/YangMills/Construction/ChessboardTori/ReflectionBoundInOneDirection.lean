import YangMills.Construction.ChessboardTori.FamiliesOfCellFunctions
import Mathlib
set_option autoImplicit false
noncomputable section
namespace YangMills.Construction.ChessboardTori
def OneAxisReflectionBound.Statement : Prop :=
  ∀ (D : ChessboardSetup) (g : ReflectionGrid D), 2 * g.cellSide ≤ PeriodicLattice.torusSide D.L D.m →
    ∀ (k₀ : Fin 4 → ℤ) (n : ℕ), (n : ℝ) = g.cellsAcross →
      ∀ (μ : Fin 4) (F : (Fin 4 → ℤ) → D.GaugeField → ℂ),
        (∀ k ∈ cubeIndexBox k₀ n, F k ∈ ReflectionGrid.cellObservables (D := D) (g.cell k)) →
        (∀ j ∈ Finset.Ico (k₀ μ) (k₀ μ + n),
          (D.familyExpectation k₀ n (g.reflectFamily μ j F)).im = 0 ∧
            0 ≤ (D.familyExpectation k₀ n (g.reflectFamily μ j F)).re) ∧
        ‖D.familyExpectation k₀ n F‖ ≤ ∏ j ∈ Finset.Ico (k₀ μ) (k₀ μ + n),
          (D.familyExpectation k₀ n (g.reflectFamily μ j F)).re ^ (1 / (n : ℝ))
end YangMills.Construction.ChessboardTori
end
