import YangMills.Construction.OneLoopLaw.CoefficientOfAFunctional
import YangMills.Construction.PeriodicOperators.TracesOfKernelsAtUnitFields
import YangMills.Construction.Towers.TheSettingOfTheRemainder
import YangMills.Construction.Towers.TransposesOfDifferencesAtScalarFunctions
import Mathlib
set_option autoImplicit false
noncomputable section
namespace YangMills.Construction.Tower.MassiveOperators
def EdgeFormIsQuotIndicator : Prop :=
  ∀ L : ℕ, Conventions.IsAdmissibleBlockingFactor L → ∀ m : ℕ, 0 < m →
    ∀ (q : EffectiveAction.IntBond) (x : Tower.FullSpace.Vertex L 0 0),
      (∀ μ, (x : InfiniteLattice.AmbientSpace) μ = (q.1 μ : ℝ)) →
      OneLoopLaw.FunctionalStiffness.liftedPauliForm L m 2 q ∈ Tower.complexEdgeForms L m 0 0 ∧
      Tower.remainderQuotField (OneLoopLaw.FunctionalStiffness.liftedPauliForm L m 2 q) =
        PeriodicOperators.UnitFieldTraces.quotIndicator (PeriodicOperators.colourEdges L 0 0)
          (2 * L ^ m) ((2 : Fin 3), Tower.FullSpace.forwardEdge x q.2)
end YangMills.Construction.Tower.MassiveOperators
end
