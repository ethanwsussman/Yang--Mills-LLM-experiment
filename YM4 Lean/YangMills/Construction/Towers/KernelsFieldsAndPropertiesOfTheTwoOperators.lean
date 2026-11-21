import YangMills.Construction.PeriodicOperators.CovariantKernelsOfFiniteRange
import YangMills.Construction.PeriodicOperators.EntriesAtTheClassesAndMapsIntoHom
import YangMills.Construction.Towers.TheMassiveFunctional
import Mathlib
set_option autoImplicit false
open Set
noncomputable section
namespace YangMills.Construction
namespace Tower
open PeriodicOperators (PeriodicData KernelMatrix IsPeriodicKernel SymbolSummableOn quotSymbol
  quotOne colourVertices colourEdges Represents IsLocalOpFun HasEntireKernelEntries
  toComplexVec bilinDot)
namespace FullSpace
variable {L : ℕ}
def gaugeLaplacianKernel (U : Edge L 0 0 → Matrices.ComplexMatrix2) :
    KernelMatrix (Fin 3 × Vertex L 0 0) (Fin 3 × Vertex L 0 0) :=
  (vertexCoordinate (Vertex L 0 0)).kernel (vertexCoordinate (Vertex L 0 0)) (gaugeLaplacian U)
def massiveHessianKernel (U : Edge L 0 0 → Matrices.ComplexMatrix2) :
    KernelMatrix (Fin 3 × PositiveEdge (meshAt L 0 0))
      (Fin 3 × PositiveEdge (meshAt L 0 0)) :=
  (edgePauliCoordinates L 0 0).kernel (edgePauliCoordinates L 0 0) (massiveHessian U)
def expField (ζ : Fin 3 × PositiveEdge (meshAt L 0 0) → ℂ) :
    Edge L 0 0 → Matrices.ComplexMatrix2 :=
  expTwist ((edgePauliCoordinates L 0 0).ofCoeffs ζ) fun _ => 1
def gaugeLaplacianAt (ζ : Fin 3 × PositiveEdge (meshAt L 0 0) → ℂ) :
    KernelMatrix (Fin 3 × Vertex L 0 0) (Fin 3 × Vertex L 0 0) :=
  gaugeLaplacianKernel (expField ζ)
def massiveHessianAt (ζ : Fin 3 × PositiveEdge (meshAt L 0 0) → ℂ) :
    KernelMatrix (Fin 3 × PositiveEdge (meshAt L 0 0))
      (Fin 3 × PositiveEdge (meshAt L 0 0)) :=
  massiveHessianKernel (expField ζ)
variable (L)
def vertexPlaneWave (q : Fin 4 → ℂ) (X : Matrices.ComplexMatrix2) :
    Vertex L 0 0 → Matrices.ComplexMatrix2 :=
  fun x => Complex.exp (Complex.I * bilinDot q (toComplexVec x)) • X
def edgePlaneWave (q : Fin 4 → ℂ) (c : Fin 4 → Matrices.ComplexMatrix2) :
    Edge L 0 0 → Matrices.ComplexMatrix2 :=
  open Classical in extendOddly fun b =>
    Complex.exp (Complex.I * bilinDot q (toComplexVec b.initial)) •
      ∑ μ, if b.terminal - b.initial = InfiniteLattice.axisStep (meshAt L 0 0) μ then c μ else 0
end FullSpace
namespace TwoOperators
structure HasLaplacianSymbol (I : PeriodicData) (T : I.Carrier → I.Carrier → ℂ) : Prop where
  periodic : IsPeriodicKernel I I T
  summable : SymbolSummableOn I I T univ
  entries : ∀ (κ : Fin 4 → ℂ) (ι' ι : I.Carrier), PeriodicOperators.fourierSymbol I I T κ ι' ι =
    Massive.latticeSymbol κ * quotOne I (I.mkQuot 1 ι') (I.mkQuot 1 ι)
  matrix : ∀ κ : Fin 4 → ℂ, quotSymbol I I T κ = Massive.latticeSymbol κ • quotOne I
structure AtIdentityOnLattice (L : ℕ) : Prop where
  laplacian_kernel : Represents (FullSpace.gaugeLaplacianKernel (L := L) fun _ => 1)
    ((vertexCoordinate (FullSpace.Vertex L 0 0)).mapOnCoeffs (vertexCoordinate (FullSpace.Vertex L 0 0))
      (FullSpace.gaugeLaplacian fun _ => 1))
  massive_kernel : Represents (FullSpace.massiveHessianKernel (L := L) fun _ => 1)
    ((FullSpace.edgePauliCoordinates L 0 0).mapOnCoeffs (FullSpace.edgePauliCoordinates L 0 0)
      (FullSpace.massiveHessian fun _ => 1))
  laplacian_symbol : HasLaplacianSymbol (colourVertices L 0 0)
    (FullSpace.gaugeLaplacianKernel (L := L) fun _ => 1)
  massive_symbol : HasLaplacianSymbol (colourEdges L 0 0)
    (FullSpace.massiveHessianKernel (L := L) fun _ => 1)
  laplacian_wave : ∀ (q : Fin 4 → ℂ) (X : Matrices.ComplexMatrix2),
    X ∈ Matrices.ComplexMatrix2.traceless →
    FullSpace.gaugeLaplacian (fun _ => 1) (FullSpace.vertexPlaneWave L q X) =
      Massive.latticeSymbol q • FullSpace.vertexPlaneWave L q X
  massive_wave : ∀ (q : Fin 4 → ℂ) (c : Fin 4 → Matrices.ComplexMatrix2),
    (∀ μ, c μ ∈ Matrices.ComplexMatrix2.traceless) →
    FullSpace.massiveHessian (fun _ => 1) (FullSpace.edgePlaneWave L q c) =
      Massive.latticeSymbol q • FullSpace.edgePlaneWave L q c
def IsNonnegReal (z : ℂ) : Prop := z.im = 0 ∧ 0 ≤ z.re
structure AtIdentityOnTorus (L m : ℕ) : Prop where
  laplacian_maps : ∀ l ∈ vertexFunctionSpace L m 0 0,
    gaugeLaplacian (trivialField L m 0 0) l ∈ vertexFunctionSpace L m 0 0
  massive_maps : ∀ B ∈ edgeFormSpace L m 0 0,
    massiveHessian (trivialField L m 0 0) B ∈ edgeFormSpace L m 0 0
  laplacian_nonneg : ∀ l ∈ vertexFunctionSpace L m 0 0,
    IsNonnegReal (traceFinsumPairing l (gaugeLaplacian (trivialField L m 0 0) l))
  massive_nonneg : ∀ B ∈ edgeFormSpace L m 0 0,
    IsNonnegReal (edgeFormPairing B (massiveHessian (trivialField L m 0 0) B))
structure IsLocalEntireRealOn (F I : PeriodicData) (ℛ : Set (F.Carrier → ℂ))
    (T : (F.Carrier → ℂ) → I.Carrier → I.Carrier → ℂ) : Prop where
  is_local : IsLocalOpFun F I I T
  entire : HasEntireKernelEntries F I I T
  real : ∀ ζ ∈ ℛ, ∀ ι' ι, (T ζ ι' ι).im = 0
def realCoeffs (L : ℕ) : Set ((colourEdges L 0 0).Carrier → ℂ) :=
  {ζ | (FullSpace.edgePauliCoordinates L 0 0).ofCoeffs ζ ∈ FullSpace.edgeFormSpace (meshAt L 0 0)}
structure CoeffMapProperties (L : ℕ) : Prop where
  field_mem : ∀ ζ : (colourEdges L 0 0).Carrier → ℂ,
    FullSpace.expField ζ ∈ FullSpace.fieldsValuedIn L 0 0 PeriodicLattice.complexGaugeGroup
  laplacian_kernel : ∀ ζ : (colourEdges L 0 0).Carrier → ℂ,
    Represents (FullSpace.gaugeLaplacianAt ζ)
      ((vertexCoordinate (FullSpace.Vertex L 0 0)).mapOnCoeffs (vertexCoordinate (FullSpace.Vertex L 0 0))
        (FullSpace.gaugeLaplacian (FullSpace.expField ζ)))
  massive_kernel : ∀ ζ : (colourEdges L 0 0).Carrier → ℂ,
    Represents (FullSpace.massiveHessianAt ζ)
      ((FullSpace.edgePauliCoordinates L 0 0).mapOnCoeffs (FullSpace.edgePauliCoordinates L 0 0)
        (FullSpace.massiveHessian (FullSpace.expField ζ)))
  laplacian_local : IsLocalEntireRealOn (colourEdges L 0 0) (colourVertices L 0 0)
    (realCoeffs L) FullSpace.gaugeLaplacianAt
  massive_local : IsLocalEntireRealOn (colourEdges L 0 0) (colourEdges L 0 0)
    (realCoeffs L) FullSpace.massiveHessianAt
end TwoOperators
end Tower
end YangMills.Construction
end
