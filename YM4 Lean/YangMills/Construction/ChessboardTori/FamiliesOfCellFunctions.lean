import YangMills.Construction.ChessboardTori.GridsCellsAndCopies
import Mathlib
set_option autoImplicit false
noncomputable section
namespace YangMills.Construction
namespace ChessboardTori
def cubeIndexBox (k₀ : Fin 4 → ℤ) (n : ℕ) : Finset (Fin 4 → ℤ) :=
  Fintype.piFinset fun μ => Finset.Ico (k₀ μ) (k₀ μ + n)
def ChessboardSetup.familyExpectation (D : ChessboardSetup) (k₀ : Fin 4 → ℤ) (n : ℕ)
    (F : (Fin 4 → ℤ) → D.GaugeField → ℂ) : ℂ :=
  D.liftedExpectation fun U => ∏ k ∈ cubeIndexBox k₀ n, F k U
namespace ReflectionGrid
variable {D : ChessboardSetup} (g : ReflectionGrid D)
def reflectFamily (μ : Fin 4) (j : ℤ) (F : (Fin 4 → ℤ) → D.GaugeField → ℂ) :
    (Fin 4 → ℤ) → D.GaugeField → ℂ :=
  fun k => g.transportTo (g.cell (Function.update k μ j)) (g.cell k) (F (Function.update k μ j))
def transportedFamily (j : Fin 4 → ℤ) (G : D.GaugeField → ℂ) :
    (Fin 4 → ℤ) → D.GaugeField → ℂ :=
  fun k => g.transportTo (g.cell j) (g.cell k) G
end ReflectionGrid
end ChessboardTori
end YangMills.Construction
end
