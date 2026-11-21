import YangMills.Construction.Towers.TheDilationOfTheMassiveFields
import YangMills.Construction.Towers.TheOperatorFunctionsOfTheMassiveFunctional
import Mathlib
set_option autoImplicit false
noncomputable section
namespace YangMills.Construction.Tower.MassiveOpFunctions.ScalingKernels
open PeriodicOperators
open Scaling
def MassiveKernelsScale : Prop :=
  ∀ (L : ℕ) (hL : 0 < L), Conventions.IsAdmissibleBlockingFactor L → ∀ k : ℕ, 1 ≤ k → ∀ z : ℝ,
    ∀ f : (colourEdges L k 0).Carrier → ℂ,
      (∀ i' i : (colourVertices L k 0).Carrier,
        scaledVertexOpFun L k z f i' i =
          ((((finestMesh L k : ℝ) : ℂ)) ^ 2)⁻¹ *
            vertexOpFun L (finestMesh L k ^ 2 * z) (scaledField hL k f)
              (scaleVertexIndex hL k i') (scaleVertexIndex hL k i)) ∧
      ∀ i' i : (colourEdges L k 0).Carrier,
        scaledEdgeOpFun L k z f i' i =
          ((((finestMesh L k : ℝ) : ℂ)) ^ 2)⁻¹ *
            edgeOpFun L (finestMesh L k ^ 2 * z) (scaledField hL k f)
              (scaleEdgeIndex hL k i') (scaleEdgeIndex hL k i)
end YangMills.Construction.Tower.MassiveOpFunctions.ScalingKernels
end
