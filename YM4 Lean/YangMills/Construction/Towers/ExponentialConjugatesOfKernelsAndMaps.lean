import YangMills.Construction.PeriodicOperators.SymbolMatricesAndPlaneWaves
import YangMills.Construction.Towers.KernelsOfThreeMapsOfATower
import Mathlib
set_option autoImplicit false
noncomputable section
namespace YangMills.Construction
namespace Tower
open PeriodicOperators
open InfiniteLattice (AmbientSpace)
namespace PauliComponentsOfSymmetricKernel
def kernelOfBasisImages (r r' : PauliComponentsOfSymmetricKernel)
    (f : (r.space.index → Matrices.ComplexMatrix2) → r'.space.index → Matrices.ComplexMatrix2) :
    KernelMatrix r.Index r'.Index :=
  open Classical in fun ι' ι => mapOnCoeffs r r' f (Pi.single ι 1) ι'
end PauliComponentsOfSymmetricKernel
structure IndexedEvaluation where
  evalOnSigma : PauliComponentsOfSymmetricKernel
  data : PeriodicData
  toIndex : data.Carrier → evalOnSigma.Index
namespace IndexedEvaluation
def vertices (L k j : ℕ) : IndexedEvaluation where
  evalOnSigma := vertexCoordinate (FullSpace.Vertex L k j)
  data := colourVertices L k j
  toIndex := id
def edgeForms (L k j : ℕ) : IndexedEvaluation where
  evalOnSigma := FullSpace.edgePauliCoordinates L k j
  data := colourEdges L k j
  toIndex := id
end IndexedEvaluation
def expConjOfMap (A A' : IndexedEvaluation) (θ : AmbientSpace)
    (f : (A.evalOnSigma.space.index → Matrices.ComplexMatrix2) →
      A'.evalOnSigma.space.index → Matrices.ComplexMatrix2) :
    A'.data.Carrier → A.data.Carrier → ℂ :=
  expConj A.data A'.data θ fun ι' ι =>
    A.evalOnSigma.kernelOfBasisImages A'.evalOnSigma f (A'.toIndex ι') (A.toIndex ι)
def expConjAtZero {N N' : Type} (T : KernelMatrix N N') : KernelMatrix N N' := T
def expConjOfMapAtZero (r r' : PauliComponentsOfSymmetricKernel)
    (f : (r.space.index → Matrices.ComplexMatrix2) → r'.space.index → Matrices.ComplexMatrix2) :
    KernelMatrix r.Index r'.Index :=
  expConjAtZero (r.kernelOfBasisImages r' f)
end Tower
end YangMills.Construction
end
