import YangMills.Construction.InfiniteLattice.OneLatticeItsConfigurationsAndMeasuresOnCompactSpaces
import YangMills.Construction.InfiniteLattice.PeriodicGibbsAndTorusLimitSets
import Mathlib
set_option autoImplicit false
open MeasureTheory
noncomputable section
namespace YangMills.Construction
open LatticePhases
namespace InfiniteLattice.PeriodicGibbsConvexCompact
def Statement : Prop :=
  ∀ D : Setup,
    periodicGibbsSet D.L D.K D.β =
        {ν : Measure (GaugeField D.mesh) | IsGibbs D.β ν ∧ IsShiftInvariant ν} ∧
      (periodicGibbsSet D.L D.K D.β).Nonempty ∧
      (∀ ν₁ ∈ periodicGibbsSet D.L D.K D.β, ∀ ν₂ ∈ periodicGibbsSet D.L D.K D.β,
        ∀ t : ℝ, 0 ≤ t → t ≤ 1 →
          ENNReal.ofReal t • ν₁ + ENNReal.ofReal (1 - t) • ν₂ ∈
            periodicGibbsSet D.L D.K D.β) ∧
      IsCompact {ρ : ProbMeasure (GaugeField D.mesh) | ρ.toMeasure ∈ periodicGibbsSet D.L D.K D.β}
end InfiniteLattice.PeriodicGibbsConvexCompact
end YangMills.Construction
end
