import YangMills.Construction.Towers.TheFunctionOfTheMassiveJets
import YangMills.Construction.Towers.TheOperatorFunctionsOfTheMassiveFunctional
import Mathlib
set_option autoImplicit false
noncomputable section
namespace YangMills.Construction.Tower.MassiveOpFunctions.Locality
open YangMills.Construction.PeriodicOperators
open YangMills.Construction.PeriodicOperators.LogDetSecondDerivs (IsRealOnRealFields)
open YangMills.Construction.Tower.FullSpace.BackgroundJets
def BaseLevelLocal (L : ℕ) (z : ℝ) : Prop :=
  IsLocalOpFun (colourEdges L 0 0) (colourVertices L 0 0) (colourVertices L 0 0)
      (vertexOpFun L z) ∧
    IsLocalOpFun (colourEdges L 0 0) (colourEdges L 0 0) (colourEdges L 0 0)
      (edgeOpFun L z) ∧
    IsRealOnRealFields (colourEdges L 0 0) (colourVertices L 0 0) (vertexOpFun L z) ∧
    IsRealOnRealFields (colourEdges L 0 0) (colourEdges L 0 0) (edgeOpFun L z) ∧
    (∀ κ : InfiniteLattice.AmbientSpace, IsUnit (symbolHom (colourVertices L 0 0) (colourVertices L 0 0)
      (coeffZero (colourEdges L 0 0) (colourVertices L 0 0) (colourVertices L 0 0)
        (vertexOpFun L z)) (toComplexVec κ) : Module.End ℂ ((colourVertices L 0 0).UnitQuot → ℂ))) ∧
    ∀ κ : InfiniteLattice.AmbientSpace, IsUnit (symbolHom (colourEdges L 0 0) (colourEdges L 0 0)
      (coeffZero (colourEdges L 0 0) (colourEdges L 0 0) (colourEdges L 0 0)
        (edgeOpFun L z)) (toComplexVec κ) : Module.End ℂ ((colourEdges L 0 0).UnitQuot → ℂ))
def LevelLocal (L k : ℕ) (z : ℝ) : Prop :=
  IsLocalOpFun (remainderIndex L k) (colourVertices L k 0) (colourVertices L k 0)
      (scaledVertexOpFun L k z) ∧
    IsLocalOpFun (remainderIndex L k) (colourEdges L k 0) (colourEdges L k 0)
      (scaledEdgeOpFun L k z) ∧
    (∀ κ : InfiniteLattice.AmbientSpace, IsUnit (symbolHom (colourVertices L k 0) (colourVertices L k 0)
      (coeffZero (remainderIndex L k) (colourVertices L k 0) (colourVertices L k 0)
        (scaledVertexOpFun L k z)) (toComplexVec κ) :
          Module.End ℂ ((colourVertices L k 0).UnitQuot → ℂ))) ∧
    (∀ κ : InfiniteLattice.AmbientSpace, IsUnit (symbolHom (colourEdges L k 0) (colourEdges L k 0)
      (coeffZero (remainderIndex L k) (colourEdges L k 0) (colourEdges L k 0)
        (scaledEdgeOpFun L k z)) (toComplexVec κ) :
          Module.End ℂ ((colourEdges L k 0).UnitQuot → ℂ))) ∧
    ∀ p : InfiniteLattice.AmbientSpace, toComplexVec p ∈ momentumPolydisc (massWidth z) →
      ∀ μPlus μMinus : Fin 4,
        JetQuad.EqAsJet (massWidth z) (toComplexVec p)
          (jetAlongResponse L k (scaledVertexOpFun L k z) (toComplexVec p) μPlus μMinus)
          (addScalarJet (vertexOperatorJet L k (toComplexVec p) μPlus μMinus) z) ∧
        JetQuad.EqAsJet (massWidth z) (toComplexVec p)
          (jetAlongResponse L k (scaledEdgeOpFun L k z) (toComplexVec p) μPlus μMinus)
          (addScalarJet (edgeOperatorJet L k (toComplexVec p) μPlus μMinus) z)
def OpFunsLocal : Prop :=
  ∀ L : ℕ, Conventions.IsAdmissibleBlockingFactor L → ∀ z : ℝ, 0 < z →
    BaseLevelLocal L z ∧ ∀ k : ℕ, 1 ≤ k → LevelLocal L k z
end YangMills.Construction.Tower.MassiveOpFunctions.Locality
end
