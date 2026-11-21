import YangMills.Construction.Towers.TheMassiveFunctional
import Mathlib
set_option autoImplicit false
open Set
noncomputable section
namespace YangMills.Construction
namespace Tower
namespace UnitGaugeDirections
open PeriodicOperators (Represents RowFinite KernelMatrix ApplySummable)
section KernelActions
variable {N : Type}
def basisFunction (i : N) : N → ℂ :=
  open Classical in fun k => if k = i then 1 else 0
def IsUniqueRowFiniteKernelAction (M : (N → ℂ) → N → ℂ) : Prop :=
  ∃ T : KernelMatrix N N, Represents T M ∧ (∀ T' : KernelMatrix N N, Represents T' M → T' = T) ∧
    (∀ j i, T j i = M (basisFunction i) j) ∧ RowFinite T
end KernelActions
section UnitLatticeData
variable (L : ℕ)
abbrev unitVertexSpace : PairedFunctionSpace := pairedFunctions (FullSpace.Vertex L 0 0)
abbrev unitEdgeSpace : PairedFunctionSpace := FullSpace.edgePairedSpace (meshAt L 0 0)
variable {L}
def incomingEdge (x : FullSpace.Vertex L 0 0) (μ : Fin 4) : FullSpace.Edge L 0 0 :=
  InfiniteLattice.Link.forwardFrom (x - InfiniteLattice.axisStep _ μ) μ
def outgoingEdge (x : FullSpace.Vertex L 0 0) (μ : Fin 4) : FullSpace.Edge L 0 0 :=
  InfiniteLattice.Link.forwardFrom x μ
def incidentEdges (x : FullSpace.Vertex L 0 0) : Set (FullSpace.Edge L 0 0) :=
  range (incomingEdge x) ∪ range (outgoingEdge x)
def positiveIncidentEdges (x : FullSpace.Vertex L 0 0) : Set (FullSpace.Edge L 0 0) :=
  {e | e.IsPositivelyOriented ∧ (e.terminal = x ∨ e.initial = x)}
def covDiffLinear (U : FullSpace.Edge L 0 0 → Matrices.ComplexMatrix2) :
    (unitVertexSpace L).complexSubmodule →ₗ[ℂ] (unitEdgeSpace L).complexSubmodule :=
  PairedFunctionSpace.linearOfValues (unitVertexSpace L) (unitEdgeSpace L) (FullSpace.covDiff U)
def EightIncidentEdges (L : ℕ) : Prop :=
  ∀ x : FullSpace.Vertex L 0 0,
    positiveIncidentEdges x = incidentEdges x ∧ (incidentEdges x).ncard = 8
def CovDiffAndAdjoint (U : FullSpace.Edge L 0 0 → Matrices.ComplexMatrix2) : Prop :=
  (∀ f ∈ (unitVertexSpace L).complexSubmodule, ∀ g ∈ (unitVertexSpace L).complexSubmodule,
    ∀ e : FullSpace.Edge L 0 0, e.IsPositivelyOriented → f e.terminal = g e.terminal →
      f e.initial = g e.initial →
      FullSpace.covDiff U f e = FullSpace.covDiff U g e) ∧
  (∀ f : (unitVertexSpace L).complexSubmodule,
    (covDiffLinear U f).1 = FullSpace.covDiff U f.1) ∧
  PairedFunctionSpace.PreservesFiniteSupport (covDiffLinear U) ∧
  PairedFunctionSpace.IsTransposeMap (covDiffLinear U)
    (PairedFunctionSpace.transposeMap (covDiffLinear U)) ∧
  ∀ A : (unitEdgeSpace L).complexSubmodule,
    FullSpace.covDiffAdjoint U A.1 =
      (PairedFunctionSpace.transposeMap (covDiffLinear U) A).1
def AdjointIsLocal (U : FullSpace.Edge L 0 0 → Matrices.ComplexMatrix2) : Prop :=
  ∀ A ∈ (unitEdgeSpace L).complexSubmodule, ∀ A' ∈ (unitEdgeSpace L).complexSubmodule,
    ∀ x : FullSpace.Vertex L 0 0,
    (∀ e ∈ incidentEdges x, A e = A' e) →
      FullSpace.covDiffAdjoint U A x = FullSpace.covDiffAdjoint U A' x
def CompositesDefined (U : FullSpace.Edge L 0 0 → Matrices.ComplexMatrix2) : Prop :=
  (∀ f ∈ (unitVertexSpace L).complexSubmodule,
    FullSpace.covDiff U f ∈ (unitEdgeSpace L).complexSubmodule ∧
      FullSpace.gaugeLaplacian U f ∈ (unitVertexSpace L).complexSubmodule) ∧
  ∀ A ∈ (unitEdgeSpace L).complexSubmodule,
    FullSpace.covDiffAdjoint U A ∈ (unitVertexSpace L).complexSubmodule ∧
      FullSpace.covDiff U (FullSpace.covDiffAdjoint U A) ∈
        (unitEdgeSpace L).complexSubmodule ∧
      ApplySummable (FullSpace.complexHessianKernel U)
        (toPauliCoeffs (FullSpace.restrictToPositiveEdges A)) ∧
      FullSpace.massiveHessian U A ∈ (unitEdgeSpace L).complexSubmodule
def CompositesAreKernels (U : FullSpace.Edge L 0 0 → Matrices.ComplexMatrix2) : Prop :=
  IsUniqueRowFiniteKernelAction
    (PauliComponentsOfSymmetricKernel.mapOnCoeffs (vertexCoordinate (FullSpace.Vertex L 0 0))
      (vertexCoordinate (FullSpace.Vertex L 0 0)) (FullSpace.gaugeLaplacian U)) ∧
  IsUniqueRowFiniteKernelAction
    (PauliComponentsOfSymmetricKernel.mapOnCoeffs (FullSpace.edgePauliCoordinates L 0 0) (FullSpace.edgePauliCoordinates L 0 0)
      (FullSpace.massiveHessian U))
end UnitLatticeData
def Claim : Prop :=
  ∀ L : ℕ, Conventions.IsAdmissibleBlockingFactor L → EightIncidentEdges L ∧
    ∀ U ∈ FullSpace.fieldsValuedIn L 0 0 PeriodicLattice.complexGaugeGroup,
      CovDiffAndAdjoint U ∧ AdjointIsLocal U ∧ CompositesDefined U ∧
        CompositesAreKernels U
end UnitGaugeDirections
end Tower
end YangMills.Construction
end
