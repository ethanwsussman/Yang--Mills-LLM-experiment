import YangMills.Construction.Towers.TheDensityOfAnAbelianField
import YangMills.Construction.Towers.TheOperatorFunctionsOfTheMassiveFunctional
import Mathlib
set_option autoImplicit false
open YangMills.Construction.OperatorCalculus YangMills.Construction.Tower.UnitLatticeL2
open YangMills.Construction.Tower.AbelianFieldDensity
noncomputable section
namespace YangMills.Construction.Tower.MassiveOpFunctions
open YangMills.Construction.PeriodicOperators
variable {L : ℕ}
def thirdPauliField (θ : FullSpace.PositiveEdge (meshAt L 0 0) → ℝ) :
    (colourEdges L 0 0).Carrier → ℂ :=
  fun κ => if κ.1 = 2 then (θ κ.2 : ℂ) else 0
def AbelianOperatorsAreOpFunValues : Prop :=
  ∀ L : ℕ, Conventions.IsAdmissibleBlockingFactor L → ∀ z : ℝ, 0 < z →
    ∀ θ : FullSpace.PositiveEdge (meshAt L 0 0) → ℝ,
      (∀ i' i : (colourVertices L 0 0).Carrier, vertexOpFun L z (thirdPauliField θ) i' i =
        matrixEntry (addScalar (laplacianOp θ) z) i' i) ∧
      (∀ i' i : (colourEdges L 0 0).Carrier, edgeOpFun L z (thirdPauliField θ) i' i =
        matrixEntry (addScalar (AbelianFieldDensity.massiveOp θ) z) i' i)
end YangMills.Construction.Tower.MassiveOpFunctions
end
