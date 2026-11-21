import YangMills.Construction.Towers.AveragesAreContractions
import YangMills.Construction.Towers.TheConstantOfTheStepsOfTheIteratedAverages
import Mathlib
set_option autoImplicit false
noncomputable section
namespace YangMills.Construction.Tower.FullSpace.IterStepsNearFree
open PeriodicOperators (colourEdges colourVertices)
open Tower.SmoothingContraction (OpNormLE)
def edgeStepKernel (L k j : ℕ) (V : Tower.FullSpace.Edge L k j → Matrices.ComplexMatrix2) :
    (colourEdges L k (j + 1)).Carrier → (colourEdges L k j).Carrier → ℂ :=
  (Tower.FullSpace.edgePauliCoordinates L k j).kernelOfBasisImages (Tower.FullSpace.edgePauliCoordinates L k (j + 1))
    fun B =>
      (L : ℝ)⁻¹ • (Tower.FullSpace.covariantSmoothingDeriv V B -
        Tower.FullSpace.crossingSmoothing L (a := Tower.meshAt L k (j + 1))
          (a' := Tower.meshAt L k j) B)
def vertexStepKernel (L k j : ℕ) (V : Tower.FullSpace.Edge L k j → Matrices.ComplexMatrix2) :
    (colourVertices L k (j + 1)).Carrier → (colourVertices L k j).Carrier → ℂ :=
  (Tower.vertexCoordinate (Tower.FullSpace.Vertex L k j)).kernelOfBasisImages
    (Tower.vertexCoordinate (Tower.FullSpace.Vertex L k (j + 1))) fun l =>
      Tower.FullSpace.adjointCubeAverage V l -
        Tower.FullSpace.vertexSmoothing L (a := Tower.meshAt L k (j + 1))
          (a' := Tower.meshAt L k j) l
def Bound : Prop :=
  ∀ L : ℕ, Conventions.IsAdmissibleBlockingFactor L → ∀ k j : ℕ, j < k →
    ∀ V ∈ Tower.FullSpace.fieldsValuedIn L k j PeriodicLattice.complexGaugeGroup,
      (∀ b, Matrices.ComplexMatrix2.operatorNorm (V b - 1) < Tower.polydiscRadius L / 2) →
      ∀ s : ℝ, (∀ b, Matrices.ComplexMatrix2.operatorNorm (V b - 1) ≤ s) →
        OpNormLE (colourEdges L k j) (colourEdges L k (j + 1))
            (edgeStepKernel L k j V) (Tower.smoothingStepConstant L * s) ∧
          OpNormLE (colourVertices L k j) (colourVertices L k (j + 1))
            (vertexStepKernel L k j V) (Tower.smoothingStepConstant L * s)
end YangMills.Construction.Tower.FullSpace.IterStepsNearFree
end
