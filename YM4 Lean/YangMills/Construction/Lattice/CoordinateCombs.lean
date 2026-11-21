import YangMills.Construction.Lattice.ContourPaths
import Mathlib
noncomputable section
namespace YangMills.Construction.PeriodicLattice
variable {L m : ℕ} {j : ℤ}
def IsChartOffset (y x : Site L m j) (d : Fin 4 → ℤ) : Prop :=
  x - y = ∑ μ, d μ • unitStep L m j μ ∧ ∀ μ, ((|d μ| : ℤ) : ℝ) * meshSize L j < torusSide L m / 2
def chartOffset (y x : Site L m j) : Fin 4 → ℤ :=
  Classical.epsilon (IsChartOffset y x)
def coordinateComb (y x : Site L m j) : List (Bond L m j) :=
  stepsThroughAxes (chartOffset y x) y [3, 2, 1, 0]
end YangMills.Construction.PeriodicLattice
