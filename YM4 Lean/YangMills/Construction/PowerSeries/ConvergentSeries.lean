import YangMills.Construction.Coordinates.HolomorphyInCoordinates
import Mathlib
open scoped ENNReal
noncomputable section
namespace YangMills.Construction
namespace PowerSeries
namespace RealSeries
variable {n : ℕ}
def realEmbed (x : Fin n → ℝ) : Coordinates.ComplexCoordinates n := fun i => (x i : ℂ)
end RealSeries
end PowerSeries
end YangMills.Construction
