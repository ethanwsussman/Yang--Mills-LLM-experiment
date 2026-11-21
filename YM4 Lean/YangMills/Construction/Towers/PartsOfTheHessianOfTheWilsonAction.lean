import YangMills.Construction.PeriodicOperators.SymmetricKernelOfAQuadraticForm
import YangMills.Construction.Towers.TransportsAroundAPlaquette
import Mathlib
set_option autoImplicit false
noncomputable section
namespace YangMills.Construction.Tower
open YangMills.Construction.Matrices YangMills.Construction.PeriodicOperators
def bracketSumOrdered (Y Z : Fin 4 → ComplexMatrix2) : ComplexMatrix2 :=
  ∑ i, ∑ j ∈ Finset.Ioi i, (Y i * Z j - Z j * Y i)
section FiniteSide
variable {L n k : ℕ}
def holonomyDefect (U b : Edge L n k 0 → ComplexMatrix2) : Face L n k 0 → ComplexMatrix2 :=
  fun p => (finestMesh L k)⁻¹ • ∑ i, transportSign i •
    (ComplexMatrix2.conjugateBy (faceTransports U p i) (b (faceEdge p i)) - b (faceEdge p i))
def halfFaceTrace (U : Edge L n k 0 → ComplexMatrix2) (p : Face L n k 0) : ℂ :=
  (1 / 2) * ComplexMatrix2.fullTrace (PeriodicLattice.plaquetteHolonomy U p)
def halfFaceTraceMul (U : Edge L n k 0 → ComplexMatrix2)
    (h : Face L n k 0 → ComplexMatrix2) : Face L n k 0 → ComplexMatrix2 :=
  fun p => halfFaceTrace U p • h p
def curvatureMatrix (U : Edge L n k 0 → ComplexMatrix2) (p : Face L n k 0) : ComplexMatrix2 :=
  (1 / (2 * Complex.I * (finestMesh L k : ℂ) ^ 2)) •
    (PeriodicLattice.plaquetteHolonomy U p - (PeriodicLattice.plaquetteHolonomy U p)⁻¹)
def curvatureBilinear (U b c : Edge L n k 0 → ComplexMatrix2) : ℂ :=
  ((finestMesh L k : ℂ) ^ 4) * ∑ᶠ p : Face L n k 0, (Complex.I / 2) *
    ComplexMatrix2.fullTrace (bracketSumOrdered (transportedForm U b p) (transportedForm U c p) *
      curvatureMatrix U p)
def IsCurvatureKernel (U : Edge L n k 0 → ComplexMatrix2)
    (X : KernelMatrix (Fin 3 × PositiveEdge L n k 0) (Fin 3 × PositiveEdge L n k 0)) : Prop :=
  IsSymmKernel (meshWeight (finestMesh L k)) X ∧
    ∀ f : finsuppFunctions (Fin 3 × PositiveEdge L n k 0),
      kernelPairing (meshWeight (finestMesh L k)) X f f =
        curvatureBilinear U
          ((edgePauliCoordinates L n k 0).ofCoeffs (f : Fin 3 × PositiveEdge L n k 0 → ℂ))
          ((edgePauliCoordinates L n k 0).ofCoeffs (f : Fin 3 × PositiveEdge L n k 0 → ℂ))
def curvatureKernel (U : Edge L n k 0 → ComplexMatrix2) :
    KernelMatrix (Fin 3 × PositiveEdge L n k 0) (Fin 3 × PositiveEdge L n k 0) :=
  Classical.epsilon (IsCurvatureKernel U)
def holonomyDefectKernel (L n k : ℕ) (U : Edge L n k 0 → ComplexMatrix2) :
    KernelMatrix (Fin 3 × PositiveEdge L n k 0) (Fin 3 × Face L n k 0) :=
  (edgePauliCoordinates L n k 0).kernel (vertexCoordinate (Face L n k 0)) (holonomyDefect U)
def halfFaceTraceKernel (L n k : ℕ) (U : Edge L n k 0 → ComplexMatrix2) :
    KernelMatrix (Fin 3 × Face L n k 0) (Fin 3 × Face L n k 0) :=
  (vertexCoordinate (Face L n k 0)).kernel (vertexCoordinate (Face L n k 0))
    (halfFaceTraceMul U)
end FiniteSide
namespace FullSpace
variable {L k : ℕ}
def holonomyDefect (U b : FullSpace.Edge L k 0 → ComplexMatrix2) : FullSpace.Face L k 0 → ComplexMatrix2 :=
  fun p => (finestMesh L k)⁻¹ • ∑ i, transportSign i •
    (ComplexMatrix2.conjugateBy (FullSpace.faceTransports U p i) (b (FullSpace.faceEdge p i)) -
      b (FullSpace.faceEdge p i))
def halfFaceTrace (U : FullSpace.Edge L k 0 → ComplexMatrix2) (p : FullSpace.Face L k 0) : ℂ :=
  (1 / 2) * ComplexMatrix2.fullTrace (FullSpace.faceVariable U p)
def halfFaceTraceMul (U : FullSpace.Edge L k 0 → ComplexMatrix2)
    (h : FullSpace.Face L k 0 → ComplexMatrix2) : FullSpace.Face L k 0 → ComplexMatrix2 :=
  fun p => halfFaceTrace U p • h p
def curvatureMatrix (U : FullSpace.Edge L k 0 → ComplexMatrix2) (p : FullSpace.Face L k 0) :
    ComplexMatrix2 :=
  (1 / (2 * Complex.I * (finestMesh L k : ℂ) ^ 2)) •
    (FullSpace.faceVariable U p - (FullSpace.faceVariable U p)⁻¹)
def curvatureBilinear (U b c : FullSpace.Edge L k 0 → ComplexMatrix2) : ℂ :=
  ((finestMesh L k : ℂ) ^ 4) * ∑ᶠ p : FullSpace.Face L k 0, (Complex.I / 2) *
    ComplexMatrix2.fullTrace
      (bracketSumOrdered (FullSpace.transportedForm U b p) (FullSpace.transportedForm U c p) *
        curvatureMatrix U p)
def IsCurvatureKernel (U : FullSpace.Edge L k 0 → ComplexMatrix2)
    (X : KernelMatrix (Fin 3 × FullSpace.PositiveEdge (meshAt L k 0))
      (Fin 3 × FullSpace.PositiveEdge (meshAt L k 0))) : Prop :=
  IsSymmKernel (meshWeight (finestMesh L k)) X ∧
    ∀ f : finsuppFunctions (Fin 3 × FullSpace.PositiveEdge (meshAt L k 0)),
      kernelPairing (meshWeight (finestMesh L k)) X f f =
        curvatureBilinear U
          ((FullSpace.edgePauliCoordinates L k 0).ofCoeffs
            (f : Fin 3 × FullSpace.PositiveEdge (meshAt L k 0) → ℂ))
          ((FullSpace.edgePauliCoordinates L k 0).ofCoeffs
            (f : Fin 3 × FullSpace.PositiveEdge (meshAt L k 0) → ℂ))
def curvatureKernel (U : FullSpace.Edge L k 0 → ComplexMatrix2) :
    KernelMatrix (Fin 3 × FullSpace.PositiveEdge (meshAt L k 0))
      (Fin 3 × FullSpace.PositiveEdge (meshAt L k 0)) :=
  Classical.epsilon (IsCurvatureKernel U)
def holonomyDefectKernel (L k : ℕ) (U : FullSpace.Edge L k 0 → ComplexMatrix2) :
    KernelMatrix (Fin 3 × FullSpace.PositiveEdge (meshAt L k 0)) (Fin 3 × FullSpace.Face L k 0) :=
  (FullSpace.edgePauliCoordinates L k 0).kernel (vertexCoordinate (FullSpace.Face L k 0)) (holonomyDefect U)
def halfFaceTraceKernel (L k : ℕ) (U : FullSpace.Edge L k 0 → ComplexMatrix2) :
    KernelMatrix (Fin 3 × FullSpace.Face L k 0) (Fin 3 × FullSpace.Face L k 0) :=
  (vertexCoordinate (FullSpace.Face L k 0)).kernel (vertexCoordinate (FullSpace.Face L k 0))
    (halfFaceTraceMul U)
end FullSpace
end YangMills.Construction.Tower
end
