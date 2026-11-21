import YangMills.Construction.Towers.TheOperatorFunctionsOfTheMassiveFunctional
import Mathlib
set_option autoImplicit false
noncomputable section
namespace YangMills.Construction.Tower.MassiveOpFunctions.LogarithmsNearIdentity
open PeriodicOperators
open PeriodicOperators.LogDetSecondDerivs
open PeriodicOperators.Tempered (EventuallyForSides)
def IdentitiesBelow (L n : ℕ) (m r : ℝ) : Prop :=
  ∀ A ∈ edgeFormSpace L n 0 0, (∀ e, Matrices.ComplexMatrix2.operatorNorm (A e) < r) →
    massiveLogDetFunctional L n m
        (PeriodicLattice.expTwist A (Tempered.identityField L n)) =
        realLogAbsDetDiff (colourEdges L 0 0) (colourVertices L 0 0) (vertexOpFun L m)
            (2 * L ^ n) (fun c => (remainderQuotField A c).re) -
          1 / 2 * realLogAbsDetDiff (colourEdges L 0 0) (colourEdges L 0 0)
            (edgeOpFun L m) (2 * L ^ n) (fun c => (remainderQuotField A c).re) ∧
    ((massiveLogDetFunctional L n m
        (PeriodicLattice.expTwist A (Tempered.identityField L n)) : ℝ) : ℂ) =
      logNormalizedDet (colourEdges L 0 0) (colourVertices L 0 0) (vertexOpFun L m)
          (2 * L ^ n) (remainderQuotField A) -
        1 / 2 * logNormalizedDet (colourEdges L 0 0) (colourEdges L 0 0)
          (edgeOpFun L m) (2 * L ^ n) (remainderQuotField A)
def Claim : Prop :=
  ∀ L : ℕ, Conventions.IsAdmissibleBlockingFactor L → ∀ m : ℝ, 0 < m →
    EventuallyForSides L fun n => ∃ r : ℝ, 0 < r ∧ IdentitiesBelow L n m r
end YangMills.Construction.Tower.MassiveOpFunctions.LogarithmsNearIdentity
end
