import YangMills.Construction.InfiniteLattice.ConnectedCorrelations
import Mathlib
set_option autoImplicit false
noncomputable section
namespace YangMills.Construction.InfiniteLattice.PeriodicExtensions
open MeasureTheory YangMills.Construction.InfiniteLattice
abbrev fourPointUrsell {a : ℝ} (μ : Measure (GaugeField a))
    (f : Fin 4 → AmbientSpace → ℝ) : ℂ :=
  ursellFunction μ 4 f
end YangMills.Construction.InfiniteLattice.PeriodicExtensions
end
