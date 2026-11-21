import YangMills.Construction.RunningCouplingSlope.PlainSaddlesOnTheWholeLattice
import Mathlib
set_option autoImplicit false
noncomputable section
namespace YangMills.Construction.RunningCouplingSlope.FullLattice
open YangMills.Construction.Tower YangMills.Construction.Tower.FullSpace YangMills.Construction.PeriodicOperators
def meanVertexStepKernel (L k : ℕ) (U : FullSpace.Edge L k 0 → Matrices.ComplexMatrix2) (m : ℕ) :
    KernelMatrix (Fin 3 × FullSpace.Vertex L k m) (Fin 3 × FullSpace.Vertex L k (m + 1)) :=
  (vertexCoordinate (FullSpace.Vertex L k m)).kernel (vertexCoordinate (FullSpace.Vertex L k (m + 1)))
    (adjointCubeAverage (meanIterate U m))
structure StepKernelConditions (L k m : ℕ) (U : FullSpace.Edge L k 0 → Matrices.ComplexMatrix2) : Prop where
  step_rowFinite : RowFinite (meanStepKernel L k U m)
  step_represents : Represents (meanStepKernel L k U m)
    (PauliComponentsOfSymmetricKernel.mapOnCoeffs (FullSpace.edgePauliCoordinates L k m) (FullSpace.edgePauliCoordinates L k (m + 1))
      fun B => (L : ℝ)⁻¹ • meanCovariantStep (meanIterate U m) B)
  vertex_rowFinite : RowFinite (meanVertexStepKernel L k U m)
  vertex_represents : Represents (meanVertexStepKernel L k U m)
    (PauliComponentsOfSymmetricKernel.mapOnCoeffs (vertexCoordinate (FullSpace.Vertex L k m))
      (vertexCoordinate (FullSpace.Vertex L k (m + 1))) (adjointCubeAverage (meanIterate U m)))
  maps_complexForms : ∀ B ∈ FullSpace.complexEdgeForms (meshAt L k m),
    meanCovariantStep (meanIterate U m) B ∈ FullSpace.complexEdgeForms (meshAt L k (m + 1))
  map_smul : ∀ B ∈ FullSpace.complexEdgeForms (meshAt L k m), ∀ w : ℂ, ∀ c : FullSpace.Edge L k (m + 1),
    c.IsPositivelyOriented → meanCovariantStep (meanIterate U m) (w • B) c =
      w • meanCovariantStep (meanIterate U m) B c
  maps_traceless : ∀ l : FullSpace.Vertex L k m → Matrices.ComplexMatrix2,
    (∀ x, l x ∈ Matrices.ComplexMatrix2.traceless) →
    ∀ y, adjointCubeAverage (meanIterate U m) l y ∈ Matrices.ComplexMatrix2.traceless
def MeanStepKernelsAreLocal : Prop :=
  ∀ L : ℕ, Conventions.IsAdmissibleBlockingFactor L → ∀ k : ℕ, 1 ≤ k →
    (∀ m : ℕ, m < k →
      IsLocalOpFun (colourEdges L k 0) (colourEdges L k m)
        (colourEdges L k (m + 1))
        (fun f => meanStepKernel L k (BackgroundJets.gaugeFieldOfForm L k f) m) ∧
      IsLocalOpFun (colourEdges L k 0) (colourEdges L k (m + 1))
        (colourEdges L k (m + 1))
        (fun f => invRadiusDiag (BackgroundJets.gaugeFieldOfForm L k f) m) ∧
      IsLocalOpFun (colourEdges L k 0) (colourVertices L k m)
        (colourVertices L k (m + 1))
        (fun f => meanVertexStepKernel L k (BackgroundJets.gaugeFieldOfForm L k f) m)) ∧
    ∃ ρ : ℝ, 0 < ρ ∧ ∀ f : (colourEdges L k 0).Carrier → ℂ,
      IsSupBelow (colourEdges L k 0) f ρ → ∀ m : ℕ, m < k →
        StepKernelConditions L k m (BackgroundJets.gaugeFieldOfForm L k f) ∧
        ((∀ κ, (f κ).im = 0) →
          (∀ ι' ι, (meanStepKernel L k (BackgroundJets.gaugeFieldOfForm L k f) m ι' ι).im = 0) ∧
          (∀ ι' ι, (invRadiusDiag (BackgroundJets.gaugeFieldOfForm L k f) m ι' ι).im = 0) ∧
          ∀ ι' ι, (meanVertexStepKernel L k (BackgroundJets.gaugeFieldOfForm L k f) m ι' ι).im = 0)
end YangMills.Construction.RunningCouplingSlope.FullLattice
end
