import YangMills.Construction.Towers.PropertiesOfPeriodicExtensionsAndPeriodisation
import YangMills.Construction.Towers.TheFieldsAndTheTwoOperatorFunctions
import Mathlib
set_option autoImplicit false
noncomputable section
namespace YangMills.Construction
namespace LocalKernels
def WeightedIndexSet.disjointUnion {k : ℕ} (I I' : WeightedIndexSet k) : WeightedIndexSet k where
  Slot := I.Slot ⊕ I'.Slot
  finite_slot := by
    have := I.finite_slot
    have := I'.finite_slot
    infer_instance
  comp := Sum.elim I.comp I'.comp
end LocalKernels
namespace GaussianConstraint
def saddlePointOperatorOfInnerCores {V V' : Type*} [AddCommGroup V] [Module ℝ V] [FiniteDimensional ℝ V]
    [AddCommGroup V'] [Module ℝ V'] [FiniteDimensional ℝ V']
    (c : InnerProductSpace.Core ℝ V) (c' : InnerProductSpace.Core ℝ V') (X : V →ₗ[ℝ] V)
    (M : V →ₗ[ℝ] V') : (V × V') →ₗ[ℝ] V × V' :=
  letI := c.toNormedAddCommGroup
  letI := InnerProductSpace.ofCore c.toCore
  letI := c'.toNormedAddCommGroup
  letI := InnerProductSpace.ofCore c'.toCore
  saddlePointOperator X M
end GaussianConstraint
namespace Tower.OperatorBlocksDescend
open PeriodicOperators (KernelMatrix applyKernel compKernel swapKernel)
open LocalKernels
open LocalKernels.Periodisation
variable {L n k : ℕ}
def saddleOnEdgeForms (X : edgeFormSpace L n k 0 →ₗ[ℝ] edgeFormSpace L n k 0)
    (M : edgeFormSpace L n k 0 →ₗ[ℝ] edgeFormSpace L n k k) :
    (edgeFormSpace L n k 0 × edgeFormSpace L n k k) →ₗ[ℝ] edgeFormSpace L n k 0 × edgeFormSpace L n k k :=
  open Classical in
  if h : EdgeFormsEuclidean L n k 0 ∧ EdgeFormsEuclidean L n k k then
    haveI := h.1.1
    haveI := h.2.1
    GaussianConstraint.saddlePointOperatorOfInnerCores h.1.2.choose h.2.2.choose X M
  else 0
def saddleOnVertexFunctions (X : vertexFunctionSpace L n k 0 →ₗ[ℝ] vertexFunctionSpace L n k 0)
    (M : vertexFunctionSpace L n k 0 →ₗ[ℝ] vertexFunctionSpace L n k k) :
    (vertexFunctionSpace L n k 0 × vertexFunctionSpace L n k k) →ₗ[ℝ]
      vertexFunctionSpace L n k 0 × vertexFunctionSpace L n k k :=
  open Classical in
  if h : VertexFunctionsEuclidean L n k 0 ∧ VertexFunctionsEuclidean L n k k then
    haveI := h.1.1
    haveI := h.2.1
    GaussianConstraint.saddlePointOperatorOfInnerCores h.1.2.choose h.2.2.choose X M
  else 0
def iterCovariantDerivTranspose (L n k : ℕ) (U : Edge L n k 0 → Matrices.ComplexMatrix2) :
    edgeFormSpace L n k k →ₗ[ℝ] edgeFormSpace L n k 0 :=
  PairedFunctionSpace.realTransposeMap (S := edgePairedSpace L n k 0) (S' := edgePairedSpace L n k k)
    (iterCovariantDerivLinear L n k U)
def covLaplacianLinear (L n k : ℕ) (U : Edge L n k 0 → Matrices.ComplexMatrix2) :
    vertexFunctionSpace L n k 0 →ₗ[ℝ] vertexFunctionSpace L n k 0 :=
  covDiffRealTranspose L n k U ∘ₗ covDiffLinear L n k U
section PauliMatrices
variable (L n)
abbrev ColourCell (A : CellClass k) : Type := Fin 3 × Cell L k A.level A.cellType
def IsPauliMatrixOf (A A' : CellClass k)
    {p : Submodule ℝ ((CellClass.quotSpace L n A).index → Matrices.ComplexMatrix2)}
    {p' : Submodule ℝ ((CellClass.quotSpace L n A').index → Matrices.ComplexMatrix2)} (m : p →ₗ[ℝ] p')
    (M : KernelMatrix (A.colourPairs.ImageCarrier L n) (A'.colourPairs.ImageCarrier L n)) : Prop :=
  ∀ f : p, CellClass.quotCoeffsOn L n A'
      (m f : (CellClass.quotSpace L n A').index → Matrices.ComplexMatrix2) =
    applyKernel M (CellClass.quotCoeffsOn L n A
      (f : (CellClass.quotSpace L n A).index → Matrices.ComplexMatrix2))
def kernelOnIdx (A A' : CellClass k) (T : KernelMatrix (ColourCell L A) (ColourCell L A')) :
    KernelMatrix (Idx L A.colourPairs) (Idx L A'.colourPairs) :=
  fun i' i => T i'.2 i.2
abbrev pairedSum (A A' : CellClass k) : WeightedIndexSet k := A.colourPairs.disjointUnion A'.colourPairs
def toSum (A A' : CellClass k) : Idx L (pairedSum A A') → ColourCell L A ⊕ ColourCell L A'
  | ⟨.inl _, i⟩ => .inl i
  | ⟨.inr _, i⟩ => .inr i
def kernelOnPairedSum (A A' : CellClass k)
    (T : KernelMatrix (ColourCell L A ⊕ ColourCell L A') (ColourCell L A ⊕ ColourCell L A')) :
    KernelMatrix (Idx L (pairedSum A A')) (Idx L (pairedSum A A')) :=
  fun i' i => T (toSum L A A' i') (toSum L A A' i)
def quotCoeffsOnPair (A A' : CellClass k)
    (f : (CellClass.quotSpace L n A).index → Matrices.ComplexMatrix2)
    (f' : (CellClass.quotSpace L n A').index → Matrices.ComplexMatrix2) :
    (pairedSum A A').ImageCarrier L n → ℂ
  | ⟨.inl _, c⟩ => CellClass.quotCoeffsOn L n A f ⟨(), c⟩
  | ⟨.inr _, c⟩ => CellClass.quotCoeffsOn L n A' f' ⟨(), c⟩
def IsPauliMatrixOfPair (A A' : CellClass k)
    {p : Submodule ℝ ((CellClass.quotSpace L n A).index → Matrices.ComplexMatrix2)}
    {p' : Submodule ℝ ((CellClass.quotSpace L n A').index → Matrices.ComplexMatrix2)}
    (m : (p × p') →ₗ[ℝ] p × p')
    (M : KernelMatrix ((pairedSum A A').ImageCarrier L n) ((pairedSum A A').ImageCarrier L n)) :
    Prop :=
  ∀ x : p × p', quotCoeffsOnPair L n A A' ((m x).1 : _ → Matrices.ComplexMatrix2)
      ((m x).2 : _ → Matrices.ComplexMatrix2) =
    applyKernel M (quotCoeffsOnPair L n A A' (x.1 : _ → Matrices.ComplexMatrix2)
      (x.2 : _ → Matrices.ComplexMatrix2))
end PauliMatrices
abbrev edgesAtTop (k : ℕ) : CellClass k := CellClass.edgeClass k k le_rfl
abbrev verticesAtTop (k : ℕ) : CellClass k := CellClass.vertexClass k k le_rfl
abbrev liftAtBase (U : Edge L n k 0 → Matrices.ComplexMatrix2) :
    FullSpace.Edge L k 0 → Matrices.ComplexMatrix2 :=
  liftGaugeField L n k 0 U
abbrev liftAtTop (μ : Edge L n k k → Matrices.ComplexMatrix2) :
    FullSpace.Edge L k k → Matrices.ComplexMatrix2 :=
  liftGaugeField L n k k μ
structure DescendsAt (L n k : ℕ) (U : Edge L n k 0 → Matrices.ComplexMatrix2)
    (J : edgeFormSpace L n k 0) (μ : edgeFormSpace L n k k) : Prop where
  hessian_descends : ∃ M, IsPauliMatrixOf L n (edgesAtZero k) (edgesAtZero k)
      (backgroundHessian U J μ) M ∧
    KernelDescends L n (edgesAtZero k).colourPairs (edgesAtZero k).colourPairs
      (kernelOnIdx L (edgesAtZero k) (edgesAtZero k)
        (FullSpace.hessianKernel (liftAtBase U)
          (liftAtBase (J : Edge L n k 0 → Matrices.ComplexMatrix2))
          (liftAtTop (μ : Edge L n k k → Matrices.ComplexMatrix2)))) M
  iterCovariant_descends : ∃ M, IsPauliMatrixOf L n (edgesAtZero k) (edgesAtTop k)
      (iterCovariantDerivLinear L n k U) M ∧
    KernelDescends L n (edgesAtZero k).colourPairs (edgesAtTop k).colourPairs
      (kernelOnIdx L (edgesAtZero k) (edgesAtTop k)
        (FullSpace.iterCovariantKernel L k (liftAtBase U))) M
  iterCovariant_swap_descends : ∃ M, IsPauliMatrixOf L n (edgesAtTop k) (edgesAtZero k)
      (iterCovariantDerivTranspose L n k U) M ∧
    KernelDescends L n (edgesAtTop k).colourPairs (edgesAtZero k).colourPairs
      (kernelOnIdx L (edgesAtTop k) (edgesAtZero k)
        (swapKernel (FullSpace.iterCovariantKernel L k (liftAtBase U)))) M
  covLaplacian_descends : ∃ M, IsPauliMatrixOf L n (verticesAtZero k) (verticesAtZero k)
      (covLaplacianLinear L n k U) M ∧
    KernelDescends L n (verticesAtZero k).colourPairs (verticesAtZero k).colourPairs
      (kernelOnIdx L (verticesAtZero k) (verticesAtZero k)
        (compKernel (swapKernel (FullSpace.covDiffKernel L k 0 (liftAtBase U)))
          (FullSpace.covDiffKernel L k 0 (liftAtBase U)))) M
  iterAverage_descends : ∃ M, IsPauliMatrixOf L n (verticesAtZero k) (verticesAtTop k)
      (iterAverageLinear L n k U) M ∧
    KernelDescends L n (verticesAtZero k).colourPairs (verticesAtTop k).colourPairs
      (kernelOnIdx L (verticesAtZero k) (verticesAtTop k)
        (FullSpace.iterAverageKernel L k (liftAtBase U))) M
  iterAverage_swap_descends : ∃ M, IsPauliMatrixOf L n (verticesAtTop k) (verticesAtZero k)
      (iterAverageRealTranspose L n k U) M ∧
    KernelDescends L n (verticesAtTop k).colourPairs (verticesAtZero k).colourPairs
      (kernelOnIdx L (verticesAtTop k) (verticesAtZero k)
        (swapKernel (FullSpace.iterAverageKernel L k (liftAtBase U)))) M
  edgeBlock_descends : ∃ M, IsPauliMatrixOfPair L n (edgesAtZero k) (edgesAtTop k)
      (saddleOnEdgeForms (backgroundHessian U J μ) (iterCovariantDerivLinear L n k U)) M ∧
    KernelDescends L n (pairedSum (edgesAtZero k) (edgesAtTop k))
      (pairedSum (edgesAtZero k) (edgesAtTop k))
      (kernelOnPairedSum L (edgesAtZero k) (edgesAtTop k)
        (FullSpace.hessianSaddle (liftAtBase U)
          (liftAtBase (J : Edge L n k 0 → Matrices.ComplexMatrix2))
          (liftAtTop (μ : Edge L n k k → Matrices.ComplexMatrix2)))) M
  vertexBlock_descends : ∃ M, IsPauliMatrixOfPair L n (verticesAtZero k) (verticesAtTop k)
      (saddleOnVertexFunctions (covLaplacianLinear L n k U) (iterAverageLinear L n k U)) M ∧
    KernelDescends L n (pairedSum (verticesAtZero k) (verticesAtTop k))
      (pairedSum (verticesAtZero k) (verticesAtTop k))
      (kernelOnPairedSum L (verticesAtZero k) (verticesAtTop k)
        (FullSpace.laplacianSaddle L k (liftAtBase U))) M
def BlocksDescend : Prop :=
  ∀ L : ℕ, Conventions.IsAdmissibleBlockingFactor L → ∀ k : ℕ, 1 ≤ k → ∀ n : ℕ, 0 < n →
    EventuallyNearIdentity (fieldSpace L n k 0) fun U => U ∈ smallIterateFields L n k ∧
      ∀ (J : edgeFormSpace L n k 0) (μ : edgeFormSpace L n k k), DescendsAt L n k U J μ
end Tower.OperatorBlocksDescend
end YangMills.Construction
end
