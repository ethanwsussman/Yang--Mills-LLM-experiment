import YangMills.Construction.Towers.TheOperatorFunctionsOfTheMassiveFunctional
import Mathlib
set_option autoImplicit false
noncomputable section
namespace YangMills.Construction.Tower.MassiveOpFunctions.PeriodicMatrices
open YangMills.Construction.PeriodicOperators
open YangMills.Construction.PeriodicOperators.LogDetSecondDerivs (quotOperator)
open YangMills.Construction.Tower.Massive (shiftedDetOn)
open YangMills.Construction.PeriodicOperators.Tempered (EventuallyForSides)
def DetsMatch (L n : ℕ) (z : ℝ) (B : Edge L n 0 0 → Matrices.ComplexMatrix2) : Prop :=
  LinearMap.det (quotOperator (colourEdges L 0 0) (colourVertices L 0 0) (vertexOpFun L z)
      (2 * L ^ n) (remainderQuotField B)) =
    ((shiftedDetOn (vertexFunctionSpace L n 0 0)
      (gaugeLaplacian (PeriodicLattice.expTwist B (PeriodicOperators.Tempered.identityField L n)))
      z : ℝ) : ℂ) ∧
  LinearMap.det (quotOperator (colourEdges L 0 0) (colourEdges L 0 0) (edgeOpFun L z)
      (2 * L ^ n) (remainderQuotField B)) =
    ((shiftedDetOn (edgeFormSpace L n 0 0)
      (massiveHessian (PeriodicLattice.expTwist B (PeriodicOperators.Tempered.identityField L n)))
      z : ℝ) : ℂ)
def DetIdentities : Prop :=
  ∀ L : ℕ, Conventions.IsAdmissibleBlockingFactor L → ∀ z : ℝ, 0 < z →
    EventuallyForSides L fun n => ∀ B ∈ edgeFormSpace L n 0 0, DetsMatch L n z B
end YangMills.Construction.Tower.MassiveOpFunctions.PeriodicMatrices
end
