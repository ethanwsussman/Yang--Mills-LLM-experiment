import YangMills.Construction.InfiniteLattice.LimitPointsOfTheTorusMeasuresArePeriodicGibbsStates
import YangMills.Construction.InfiniteLattice.TorusConfigurationsAsPeriodicConfigurations
import YangMills.Construction.InfiniteLattice.TorusStatesAsPeriodicMeasures
import Mathlib
set_option autoImplicit false
open MeasureTheory
noncomputable section
namespace YangMills.Construction.InfiniteLattice
theorem torusWeakLimitsArePeriodicGibbs_holds (hFields : TorusFieldsAsPeriodic.Statement)
    (hStates : TorusStatesAsPeriodic.Statement) : TorusWeakLimitsArePeriodicGibbs := by
  intro L K hL hK β hβ
  let s : Conventions.StandingParameters := ⟨L, hL, ⟨K, hK⟩, 1⟩
  obtain ⟨-, -, -, hLimits, -, hGibbs⟩ := hFields s β hβ
  obtain ⟨-, -, hShift⟩ := hStates s β hβ
  have key : ∀ ν ∈ GrowthCondition.torusWeakLimits L K β,
      IsPeriodicGibbs β ν ∧ IsShiftInvariant ν := by
    intro ν hν
    let ρ : PeriodicExtensions.RealWeakState (PeriodicLattice.meshSize L (K : ℤ)) := ⟨ν, hν.1⟩
    have hρ := (hLimits ρ).1.mp hν
    exact ⟨hGibbs ρ hρ, (hShift ν ((hLimits ρ).2.mpr hρ)).2⟩
  exact ⟨fun ν hν => ⟨(key ν hν).1.1, (key ν hν).2, (key ν hν).1.2⟩, fun ν hν => (key ν hν).1⟩
end YangMills.Construction.InfiniteLattice
end
