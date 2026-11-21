import YangMills.Construction.Towers.KernelsOfThreeMapsOfATower
import Mathlib
set_option autoImplicit false
noncomputable section
namespace YangMills.Construction.Tower
def CoboundariesAtIdentity : Prop :=
  ∀ L : ℕ, Conventions.IsAdmissibleBlockingFactor L →
    (∀ l ∈ (vertexCoordinate (FullSpace.Vertex L 0 0)).space.complexSubmodule,
      FullSpace.covDiff (fun _ : FullSpace.Edge L 0 0 => (1 : Matrices.ComplexMatrix2)) l =
        FullSpace.vertexCoboundary l) ∧
    ∀ B ∈ FullSpace.complexEdgeForms (meshAt L 0 0),
      FullSpace.complexHessianOperator
          (fun _ : FullSpace.Edge L 0 0 => (1 : Matrices.ComplexMatrix2)) B =
        PairedFunctionSpace.transposeOfValues (FullSpace.edgePauliCoordinates L 0 0).space
          (vertexCoordinate (FullSpace.Face L 0 0)).space FullSpace.edgeCoboundary
          (FullSpace.edgeCoboundary B)
end YangMills.Construction.Tower
end
