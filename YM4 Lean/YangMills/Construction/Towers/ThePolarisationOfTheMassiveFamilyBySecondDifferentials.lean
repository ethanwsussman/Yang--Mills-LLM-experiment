import YangMills.Construction.Towers.TheOperatorFunctionsOfTheMassiveFunctional
import Mathlib
set_option autoImplicit false
noncomputable section
namespace YangMills.Construction.Tower.MassiveOpFunctions.HessianBySecondDerivs
open YangMills.Construction.PeriodicOperators
open YangMills.Construction.PeriodicOperators.LogDetSecondDerivs
open YangMills.Construction.PeriodicOperators.Tempered (EventuallyForSides complexHessian)
def HessianIdentity : Prop :=
  ∀ L : ℕ, Conventions.IsAdmissibleBlockingFactor L → ∀ z : ℝ, 0 < z →
    EventuallyForSides L fun n =>
      ∀ (N : ℕ) (e : Fin N ≃ (colourEdges L 0 0).QuotMod (2 * L ^ n)),
        ∀ B ∈ complexEdgeForms L n 0 0, ∀ B' ∈ complexEdgeForms L n 0 0,
          complexHessian (massiveFieldFamily L z) n B B' =
            logDetSecondDeriv (colourEdges L 0 0) (colourVertices L 0 0)
                (vertexOpFun L z) e (remainderQuotField B) (remainderQuotField B') -
              1 / 2 * logDetSecondDeriv (colourEdges L 0 0) (colourEdges L 0 0)
                (edgeOpFun L z) e (remainderQuotField B) (remainderQuotField B')
end YangMills.Construction.Tower.MassiveOpFunctions.HessianBySecondDerivs
end
