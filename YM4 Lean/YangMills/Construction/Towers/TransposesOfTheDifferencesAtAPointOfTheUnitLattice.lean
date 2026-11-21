import YangMills.Construction.Towers.KernelsOfThreeMapsOfATower
import Mathlib
set_option autoImplicit false
noncomputable section
namespace YangMills.Construction.Tower.UnitLatticeAdjoints
def vertexCoboundaryAdjoint (L : ℕ) (b : FullSpace.Edge L 0 0 → Matrices.ComplexMatrix2) :
    FullSpace.Vertex L 0 0 → Matrices.ComplexMatrix2 :=
  PairedFunctionSpace.transposeOfValues (pairedFunctions (FullSpace.Vertex L 0 0))
    (FullSpace.edgePairedSpace (meshAt L 0 0)) (FullSpace.vertexCoboundary (a := meshAt L 0 0)) b
def edgeCoboundaryAdjoint (L : ℕ) (f : FullSpace.Face L 0 0 → Matrices.ComplexMatrix2) :
    FullSpace.Edge L 0 0 → Matrices.ComplexMatrix2 :=
  PairedFunctionSpace.transposeOfValues (FullSpace.edgePairedSpace (meshAt L 0 0))
    (pairedFunctions (FullSpace.Face L 0 0))
    (FullSpace.edgeCoboundary (a := meshAt L 0 0)) f
def AdjointFormulas : Prop :=
  ∀ L : ℕ, Conventions.IsAdmissibleBlockingFactor L →
    (∀ b ∈ FullSpace.complexEdgeForms (meshAt L 0 0), ∀ x : FullSpace.Vertex L 0 0,
      vertexCoboundaryAdjoint L b x =
        ∑ μ : Fin 4, (b (InfiniteLattice.Link.forwardFrom (x - InfiniteLattice.axisStep (meshAt L 0 0) μ) μ) -
          b (InfiniteLattice.Link.forwardFrom x μ))) ∧
    (∀ f ∈ Matrices.GroupLieProduct.tracelessFunctions (FullSpace.Face L 0 0),
      ∀ (x : FullSpace.Vertex L 0 0) (μ : Fin 4),
        edgeCoboundaryAdjoint L f (InfiniteLattice.Link.forwardFrom x μ) =
          (∑ ν : {ν : Fin 4 // μ < ν},
            (f ⟨x, μ, ν.1, ν.2⟩ - f ⟨x - InfiniteLattice.axisStep (meshAt L 0 0) ν.1, μ, ν.1, ν.2⟩)) -
          ∑ ν : {ν : Fin 4 // ν < μ},
            (f ⟨x, ν.1, μ, ν.2⟩ - f ⟨x - InfiniteLattice.axisStep (meshAt L 0 0) ν.1, ν.1, μ, ν.2⟩))
end YangMills.Construction.Tower.UnitLatticeAdjoints
end
