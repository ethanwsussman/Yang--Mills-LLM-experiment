import YangMills.Construction.Towers.TheDilationOfTheMassiveFields
import YangMills.Construction.Towers.TheOperatorFunctionsOfTheMassiveFunctional
import Mathlib
set_option autoImplicit false
noncomputable section
namespace YangMills.Construction.Tower.MassiveOpFunctions.ScaledSecondDerivs
open YangMills.Construction.PeriodicOperators
open YangMills.Construction.PeriodicOperators.LogDetSecondDerivs
open YangMills.Construction.Tower.MassiveOpFunctions.Scaling
open YangMills.Construction.PeriodicOperators.Tempered (EventuallyForSides)
def ScalingInvariance : Prop :=
  ∀ (L : ℕ) (hL : 0 < L), Conventions.IsAdmissibleBlockingFactor L → ∀ k : ℕ, 1 ≤ k → ∀ z : ℝ, 0 < z →
    EventuallyForSides L fun n =>
      ∀ (N : ℕ) (e : Fin N ≃ (colourEdges L k 0).QuotMod (2 * L ^ n)),
        ∃ e' : Fin N ≃ (colourEdges L 0 0).QuotMod (2 * L ^ (n + k)),
          ∀ ζ ζ' : (colourEdges L k 0).QuotMod (2 * L ^ n) → ℂ,
            logDetSecondDeriv (colourEdges L k 0) (colourVertices L k 0)
                (scaledVertexOpFun L k z) e ζ ζ' =
              logDetSecondDeriv (colourEdges L 0 0) (colourVertices L 0 0)
                (vertexOpFun L (finestMesh L k ^ 2 * z)) e'
                (scaledQuotField hL k n ζ) (scaledQuotField hL k n ζ') ∧
            logDetSecondDeriv (colourEdges L k 0) (colourEdges L k 0)
                (scaledEdgeOpFun L k z) e ζ ζ' =
              logDetSecondDeriv (colourEdges L 0 0) (colourEdges L 0 0)
                (edgeOpFun L (finestMesh L k ^ 2 * z)) e'
                (scaledQuotField hL k n ζ) (scaledQuotField hL k n ζ')
end YangMills.Construction.Tower.MassiveOpFunctions.ScaledSecondDerivs
end
