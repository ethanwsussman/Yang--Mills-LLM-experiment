import YangMills.Construction.ChessboardTori.FamiliesOfCellFunctions
import Mathlib
set_option autoImplicit false
noncomputable section
namespace YangMills.Construction.ChessboardTori
def FamilyChessboardBound.Statement : Prop :=
  ∀ (D : ChessboardSetup) (g : ReflectionGrid D),
    2 * g.cellSide ≤ PeriodicLattice.torusSide D.L D.m →
    ∀ (k₀ : Fin 4 → ℤ) (n : ℕ), (n : ℝ) = g.cellsAcross →
      ∀ F : (Fin 4 → ℤ) → D.GaugeField → ℂ,
        (∀ k ∈ cubeIndexBox k₀ n, F k ∈ ReflectionGrid.cellObservables (D := D) (g.cell k)) →
        (∀ j ∈ cubeIndexBox k₀ n,
          (D.familyExpectation k₀ n (g.transportedFamily j (F j))).im = 0 ∧
            0 ≤ (D.familyExpectation k₀ n (g.transportedFamily j (F j))).re) ∧
        ‖D.familyExpectation k₀ n F‖ ≤ ∏ j ∈ cubeIndexBox k₀ n,
          (D.familyExpectation k₀ n (g.transportedFamily j (F j))).re ^ (1 / (n : ℝ) ^ 4)
end YangMills.Construction.ChessboardTori
end
