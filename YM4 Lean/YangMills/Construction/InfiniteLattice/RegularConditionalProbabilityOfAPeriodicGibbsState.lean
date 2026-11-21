import YangMills.Construction.InfiniteLattice.OneLatticeItsConfigurationsAndMeasuresOnCompactSpaces
import YangMills.Construction.InfiniteLattice.PeriodicGibbsAndTorusLimitSets
import Mathlib
set_option autoImplicit false
open MeasureTheory YangMills.Construction.InfiniteLattice
noncomputable section
namespace YangMills.Construction.LatticePhases
variable (D : Setup)
def IsInvariantConditionalFamily (ν : periodicGibbsSet D.L D.K D.β)
    (κ : GaugeField D.mesh → ProbMeasure (GaugeField D.mesh)) : Prop :=
  ∀ F : GaugeField D.mesh → ℂ, IsBoundedObservable F →
    Measurable[shiftInvariantSigma D.mesh] (fun U => (κ U).eval F) ∧
      ∀ J : GaugeField D.mesh → ℂ, Measurable[shiftInvariantSigma D.mesh] J →
        (∃ C : ℝ, ∀ U, ‖J U‖ ≤ C) →
          ∫ U, J U * (κ U).eval F ∂ν.1 = ∫ U, J U * F U ∂ν.1
end YangMills.Construction.LatticePhases
