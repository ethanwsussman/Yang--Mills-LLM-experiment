import YangMills.Construction.Towers.ExpansionOfTheIterateInTheLeftChart
import YangMills.Construction.Towers.GaussianIntegralsAndTheNormalisers
import YangMills.Construction.Towers.TermOfTheSecondOrderAndCommutatorTerm
import Mathlib
set_option autoImplicit false
noncomputable section
namespace YangMills.Construction
namespace GaussianConstraint
def saddleDetOfCores {V W : Type*} [AddCommGroup V] [Module ℝ V] [FiniteDimensional ℝ V]
    [AddCommGroup W] [Module ℝ W] [FiniteDimensional ℝ W]
    (c : InnerProductSpace.Core ℝ V) (c' : InnerProductSpace.Core ℝ W) (X : V →ₗ[ℝ] V)
    (M : V →ₗ[ℝ] W) : ℝ :=
  letI := c.toNormedAddCommGroup
  letI := InnerProductSpace.ofCore c.toCore
  letI := c'.toNormedAddCommGroup
  letI := InnerProductSpace.ofCore c'.toCore
  LinearMap.det (saddlePointOperator X M)
end GaussianConstraint
namespace Tower
variable {L n k : ℕ}
def linearMapWithValues {α β : Type*} (p : Submodule ℝ (α → Matrices.ComplexMatrix2))
    (q : Submodule ℝ (β → Matrices.ComplexMatrix2))
    (f : (α → Matrices.ComplexMatrix2) → β → Matrices.ComplexMatrix2) : p →ₗ[ℝ] q :=
  Classical.epsilon fun T : p →ₗ[ℝ] q => ∀ x : p, (T x : β → Matrices.ComplexMatrix2) = f x
def IsVertexPairingCore {j : ℕ} (c : InnerProductSpace.Core ℝ (vertexFunctionSpace L n k j)) :
    Prop :=
  ∀ l l' : vertexFunctionSpace L n k j,
    c.inner l l' = (traceFinsumPairing (l : Vertex L n k j → Matrices.ComplexMatrix2)
      (l' : Vertex L n k j → Matrices.ComplexMatrix2)).re
def VertexFunctionsEuclidean (L n k j : ℕ) : Prop :=
  FiniteDimensional ℝ (vertexFunctionSpace L n k j) ∧
    ∃ c : InnerProductSpace.Core ℝ (vertexFunctionSpace L n k j), IsVertexPairingCore c
def saddleDetOnEdgeForms (X : edgeFormSpace L n k 0 →ₗ[ℝ] edgeFormSpace L n k 0)
    (M : edgeFormSpace L n k 0 →ₗ[ℝ] edgeFormSpace L n k k) : ℝ :=
  open Classical in
  if h : EdgeFormsEuclidean L n k 0 ∧ EdgeFormsEuclidean L n k k then
    haveI := h.1.1
    haveI := h.2.1
    GaussianConstraint.saddleDetOfCores h.1.2.choose h.2.2.choose X M
  else 0
def saddleDetOnVertexFunctions
    (X : vertexFunctionSpace L n k 0 →ₗ[ℝ] vertexFunctionSpace L n k 0)
    (M : vertexFunctionSpace L n k 0 →ₗ[ℝ] vertexFunctionSpace L n k k) : ℝ :=
  open Classical in
  if h : VertexFunctionsEuclidean L n k 0 ∧ VertexFunctionsEuclidean L n k k then
    haveI := h.1.1
    haveI := h.2.1
    GaussianConstraint.saddleDetOfCores h.1.2.choose h.2.2.choose X M
  else 0
def covDiffLinear (L n k : ℕ) (U : Edge L n k 0 → Matrices.ComplexMatrix2) :
    vertexFunctionSpace L n k 0 →ₗ[ℝ] edgeFormSpace L n k 0 :=
  linearMapWithValues _ _ (covDiff U)
def covDiffRealTranspose (L n k : ℕ) (U : Edge L n k 0 → Matrices.ComplexMatrix2) :
    edgeFormSpace L n k 0 →ₗ[ℝ] vertexFunctionSpace L n k 0 :=
  PairedFunctionSpace.realTransposeMap (S := pairedFunctions (Vertex L n k 0))
    (S' := edgePairedSpace L n k 0) (covDiffLinear L n k U)
def iterAverageLinear (L n k : ℕ) (U : Edge L n k 0 → Matrices.ComplexMatrix2) :
    vertexFunctionSpace L n k 0 →ₗ[ℝ] vertexFunctionSpace L n k k :=
  linearMapWithValues _ _ (iterAdjointCubeAverage L n k U k)
def iterAverageRealTranspose (L n k : ℕ) (U : Edge L n k 0 → Matrices.ComplexMatrix2) :
    vertexFunctionSpace L n k k →ₗ[ℝ] vertexFunctionSpace L n k 0 :=
  PairedFunctionSpace.realTransposeMap (S := pairedFunctions (Vertex L n k 0))
    (S' := pairedFunctions (Vertex L n k k)) (iterAverageLinear L n k U)
def iterCovariantDerivLinear (L n k : ℕ) (U : Edge L n k 0 → Matrices.ComplexMatrix2) :
    edgeFormSpace L n k 0 →ₗ[ℝ] edgeFormSpace L n k k :=
  linearMapWithValues _ _ (iterCovariantDeriv L n k U k)
def extendByZero (g : Vertex L n k k → Matrices.ComplexMatrix2) :
    Vertex L n k 0 → Matrices.ComplexMatrix2 :=
  open Classical in
  fun x => if h : ∃ y : Vertex L n k k, (y : PeriodicLattice.FourTorus L n) = x then g h.choose
    else 0
def backgroundGaugeParameter (U B : Edge L n k 0 → Matrices.ComplexMatrix2) :
    Vertex L n k 0 → Matrices.ComplexMatrix2 :=
  extendByZero (iterContourLogDrift L n k U k B)
def backgroundShift (L n k : ℕ) (U : Edge L n k 0 → Matrices.ComplexMatrix2) :
    edgeFormSpace L n k 0 →ₗ[ℝ] edgeFormSpace L n k 0 :=
  linearMapWithValues _ _ fun B => B + covDiff U (backgroundGaugeParameter U B)
def sourceQuadraticForm (U : Edge L n k 0 → Matrices.ComplexMatrix2) (J : edgeFormSpace L n k 0)
    (μ : edgeFormSpace L n k k) (B : edgeFormSpace L n k 0) : ℝ :=
  2 * (edgeFormPairing (J : Edge L n k 0 → Matrices.ComplexMatrix2)
      (bracketTerm U (backgroundGaugeParameter U B) B)).re +
    (edgeFormPairing (J : Edge L n k 0 → Matrices.ComplexMatrix2)
      (bracketTerm U (backgroundGaugeParameter U B)
        (covDiff U (backgroundGaugeParameter U B)))).re -
    (traceFinsumPairing (restrictToPositiveEdges (μ : Edge L n k k → Matrices.ComplexMatrix2))
      (iterQuadraticTerm U (backgroundShift L n k U B) (backgroundShift L n k U B))).re
def gaugeSliceResidual (U : Edge L n k 0 → Matrices.ComplexMatrix2) (B : edgeFormSpace L n k 0) :
    vertexFunctionSpace L n k 0 :=
  covDiffRealTranspose L n k U B -
    ((L : ℝ) ^ (4 * k)) • iterAverageRealTranspose L n k U
      (iterAverageLinear L n k U (covDiffRealTranspose L n k U B))
def backgroundHessianForm (U : Edge L n k 0 → Matrices.ComplexMatrix2)
    (J : edgeFormSpace L n k 0) (μ : edgeFormSpace L n k k) (B : edgeFormSpace L n k 0) : ℝ :=
  leftSecondDeriv (plaquetteAction L n k) U B B + sourceQuadraticForm U J μ B +
    traceFinsumNorm (gaugeSliceResidual U B : Vertex L n k 0 → Matrices.ComplexMatrix2) ^ 2
def IsBackgroundHessian (U : Edge L n k 0 → Matrices.ComplexMatrix2) (J : edgeFormSpace L n k 0)
    (μ : edgeFormSpace L n k k) (X : edgeFormSpace L n k 0 →ₗ[ℝ] edgeFormSpace L n k 0) : Prop :=
  (∀ B B' : edgeFormSpace L n k 0,
    edgeFormPairing (B : Edge L n k 0 → Matrices.ComplexMatrix2)
        (X B' : Edge L n k 0 → Matrices.ComplexMatrix2) =
      edgeFormPairing (X B : Edge L n k 0 → Matrices.ComplexMatrix2)
        (B' : Edge L n k 0 → Matrices.ComplexMatrix2)) ∧
    ∀ B : edgeFormSpace L n k 0,
      edgeFormPairing (B : Edge L n k 0 → Matrices.ComplexMatrix2)
          (X B : Edge L n k 0 → Matrices.ComplexMatrix2) =
        (backgroundHessianForm U J μ B : ℂ)
def backgroundHessian (U : Edge L n k 0 → Matrices.ComplexMatrix2) (J : edgeFormSpace L n k 0)
    (μ : edgeFormSpace L n k k) : edgeFormSpace L n k 0 →ₗ[ℝ] edgeFormSpace L n k 0 :=
  Classical.epsilon (IsBackgroundHessian U J μ)
def hessianSaddleDet (U : Edge L n k 0 → Matrices.ComplexMatrix2) (J : edgeFormSpace L n k 0)
    (μ : edgeFormSpace L n k k) : ℝ :=
  saddleDetOnEdgeForms (backgroundHessian U J μ) (iterCovariantDerivLinear L n k U)
def ghostSaddleDet (L n k : ℕ) (U : Edge L n k 0 → Matrices.ComplexMatrix2) : ℝ :=
  saddleDetOnVertexFunctions (covDiffRealTranspose L n k U ∘ₗ covDiffLinear L n k U)
    (iterAverageLinear L n k U)
def BackgroundFunctionalWellDefined (U : Edge L n k 0 → Matrices.ComplexMatrix2)
    (J : edgeFormSpace L n k 0) (μ : edgeFormSpace L n k k) : Prop :=
  hessianSaddleDet U J μ ≠ 0 ∧ ghostSaddleDet L n k U ≠ 0
def backgroundFunctional (U : Edge L n k 0 → Matrices.ComplexMatrix2) (J : edgeFormSpace L n k 0)
    (μ : edgeFormSpace L n k k) : ℝ :=
  -(1 / 2) * Real.log |hessianSaddleDet U J μ| + Real.log |ghostSaddleDet L n k U|
end Tower
end YangMills.Construction
end
