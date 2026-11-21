import YangMills.Construction.Towers.KernelsOfThreeMapsOfATower
import Mathlib
set_option autoImplicit false
open Set
noncomputable section
namespace YangMills.Construction
open Matrices (ComplexMatrix2)
namespace PeriodicOperators
def saddleMatrix {N N' : Type} (X : KernelMatrix N N) (Mt : KernelMatrix N' N)
    (M : KernelMatrix N N') : KernelMatrix (N ⊕ N') (N ⊕ N') :=
  fun ι' ι => match ι', ι with
    | .inl i', .inl i => X i' i
    | .inl i', .inr c => Mt i' c
    | .inr c', .inl i => M c' i
    | .inr _, .inr _ => 0
end PeriodicOperators
namespace Tower
open PeriodicOperators (KernelMatrix compKernel saddleMatrix swapKernel)
section Colours
variable {σ σ' : Type}
def pauliNorm (X : ComplexMatrix2) : ℝ := Real.sqrt (∑ a, ‖pauliCoeff a X‖ ^ 2)
def pauliFamilyNorm {ι : Type} [Fintype ι] (F : ι → ComplexMatrix2) : ℝ :=
  Real.sqrt (∑ i, pauliNorm (F i) ^ 2)
def meshWeight (a : ℝ) : Fin 3 × σ → ℝ := fun _ => a ^ 4
def meshPairing (a : ℝ) (f g : σ → ComplexMatrix2) : ℂ :=
  PeriodicOperators.wPairing (meshWeight a) (toPauliCoeffs f) (toPauliCoeffs g)
def meshNorm (a : ℝ) (f : σ → ComplexMatrix2) : ℝ :=
  PeriodicOperators.wNorm (meshWeight a) (toPauliCoeffs f)
def meshTranspose (a a' : ℝ) (T : KernelMatrix (Fin 3 × σ) (Fin 3 × σ')) :
    KernelMatrix (Fin 3 × σ') (Fin 3 × σ) :=
  PeriodicOperators.wTranspose (meshWeight a) (meshWeight a') T
def IsColourTrivial (T : KernelMatrix (Fin 3 × σ) (Fin 3 × σ')) : Prop :=
  (∀ (a a' : Fin 3) (y : σ') (x : σ), a' ≠ a → T (a', y) (a, x) = 0) ∧
    ∀ (a a' : Fin 3) (y : σ') (x : σ), T (a, y) (a, x) = T (a', y) (a', x)
def IsColourTrivialOnClasses {C C' : Type} (c : Fin 3 × σ → C) (c' : Fin 3 × σ' → C')
    (M : KernelMatrix C C') : Prop :=
  IsColourTrivial fun ι' ι => M (c' ι') (c ι)
end Colours
structure RescaledOperators (S₀ B₀ S B : Type) where
  eta : ℝ
  coarse : ℝ
  D : KernelMatrix (Fin 3 × S₀) (Fin 3 × B₀)
  Q : KernelMatrix (Fin 3 × B₀) (Fin 3 × B)
  R : KernelMatrix (Fin 3 × S₀) (Fin 3 × S)
  H : KernelMatrix (Fin 3 × B₀) (Fin 3 × B₀)
namespace RescaledOperators
variable {S₀ B₀ S B : Type} (p : RescaledOperators S₀ B₀ S B)
def Dt : KernelMatrix (Fin 3 × B₀) (Fin 3 × S₀) := meshTranspose p.eta p.eta p.D
def Qt : KernelMatrix (Fin 3 × B) (Fin 3 × B₀) := meshTranspose p.eta p.coarse p.Q
def Rt : KernelMatrix (Fin 3 × S) (Fin 3 × S₀) := meshTranspose p.eta p.coarse p.R
def K : KernelMatrix (Fin 3 × B₀) (Fin 3 × B₀) := p.H + compKernel p.D p.Dt
def Delta : KernelMatrix (Fin 3 × S₀) (Fin 3 × S₀) := compKernel p.Dt p.D
def Xi : KernelMatrix (Fin 3 × B₀) (Fin 3 × B₀) :=
  p.K - compKernel (compKernel p.D p.Rt) (compKernel p.R p.Dt) + compKernel p.Qt p.Q
def Y : KernelMatrix (Fin 3 × S₀) (Fin 3 × S₀) := p.Delta + compKernel p.Rt p.R
def X : KernelMatrix (Fin 3 × B₀) (Fin 3 × B₀) := p.Xi - compKernel p.Qt p.Q
def saddleX : KernelMatrix (Fin 3 × B₀ ⊕ Fin 3 × B) (Fin 3 × B₀ ⊕ Fin 3 × B) :=
  saddleMatrix p.X p.Qt p.Q
def saddleDelta : KernelMatrix (Fin 3 × S₀ ⊕ Fin 3 × S) (Fin 3 × S₀ ⊕ Fin 3 × S) :=
  saddleMatrix p.Delta p.Rt p.R
end RescaledOperators
section FiniteSide
variable {L m k j : ℕ}
abbrev scaledVertexSpace (L m k j : ℕ) : Submodule ℂ (Vertex L m k j → ComplexMatrix2) :=
  Matrices.GroupLieProduct.tracelessFunctions (Vertex L m k j)
abbrev scaledEdgeSpace (L m k j : ℕ) : Submodule ℂ (PositiveEdge L m k j → ComplexMatrix2) :=
  Matrices.GroupLieProduct.tracelessFunctions (PositiveEdge L m k j)
def scaledVertexCoboundary (l : Vertex L m k j → ComplexMatrix2) : Edge L m k j → ComplexMatrix2 :=
  (meshAt L k j)⁻¹ • vertexCoboundary l
def scaledEdgeCoboundary (B : Edge L m k j → ComplexMatrix2) : Face L m k j → ComplexMatrix2 :=
  (meshAt L k j)⁻¹ • edgeCoboundary B
def covDiffKernel (L m k j : ℕ) (W : Edge L m k j → ComplexMatrix2) :
    KernelMatrix (Fin 3 × Vertex L m k j) (Fin 3 × PositiveEdge L m k j) :=
  (vertexCoordinate (Vertex L m k j)).kernel (edgePauliCoordinates L m k j) (covDiff W)
def iterCovariantKernel (L m k : ℕ) (U : Edge L m k 0 → ComplexMatrix2) :
    KernelMatrix (Fin 3 × PositiveEdge L m k 0) (Fin 3 × PositiveEdge L m k k) :=
  (edgePauliCoordinates L m k 0).kernel (edgePauliCoordinates L m k k) (iterCovariantDeriv L m k U k)
def iterAverageKernel (L m k : ℕ) (U : Edge L m k 0 → ComplexMatrix2) :
    KernelMatrix (Fin 3 × Vertex L m k 0) (Fin 3 × Vertex L m k k) :=
  (vertexCoordinate (Vertex L m k 0)).kernel (vertexCoordinate (Vertex L m k k))
    (iterAdjointCubeAverage L m k U k)
def rescaledOperators (L m k : ℕ) (U : Edge L m k 0 → ComplexMatrix2) :
    RescaledOperators (Vertex L m k 0) (PositiveEdge L m k 0) (Vertex L m k k)
      (PositiveEdge L m k k) where
  eta := finestMesh L k
  coarse := meshAt L k k
  D := (vertexCoordinate (Vertex L m k 0)).kernel (edgePauliCoordinates L m k 0)
    fun l => (finestMesh L k)⁻¹ • covDiff U l
  Q := (edgePauliCoordinates L m k 0).kernel (edgePauliCoordinates L m k k)
    fun B => finestMesh L k • iterCovariantDeriv L m k U k B
  R := iterAverageKernel L m k U
  H := fun ι ι' => (((finestMesh L k ^ 4)⁻¹ : ℝ) : ℂ) *
    complexActionHessian U (finestMesh L k • basisForm ι.1 ι.2)
      (finestMesh L k • basisForm ι'.1 ι'.2)
def covDiffTranspose (L m k : ℕ) (U : Edge L m k 0 → ComplexMatrix2) :
    (Edge L m k 0 → ComplexMatrix2) → Vertex L m k 0 → ComplexMatrix2 :=
  PairedFunctionSpace.transposeOfValues (pairedFunctions (Vertex L m k 0)) (edgePairedSpace L m k 0)
    (covDiff U)
def iterAverageTranspose (L m k : ℕ) (U : Edge L m k 0 → ComplexMatrix2) :
    (Vertex L m k k → ComplexMatrix2) → Vertex L m k 0 → ComplexMatrix2 :=
  PairedFunctionSpace.transposeOfValues (pairedFunctions (Vertex L m k 0))
    (pairedFunctions (Vertex L m k k)) (iterAdjointCubeAverage L m k U k)
def gaugeFixingTerm (L m k : ℕ) (U B : Edge L m k 0 → ComplexMatrix2) :
    Vertex L m k 0 → ComplexMatrix2 :=
  covDiffTranspose L m k U B -
    ((L : ℝ) ^ (4 * k)) • iterAverageTranspose L m k U
      (iterAdjointCubeAverage L m k U k (covDiffTranspose L m k U B))
def backgroundForm (L m k : ℕ) (U B B' : Edge L m k 0 → ComplexMatrix2) : ℂ :=
  complexActionHessian U B B' +
    traceFinsumPairing (gaugeFixingTerm L m k U B) (gaugeFixingTerm L m k U B')
def backgroundKernel (L m k : ℕ) (U : Edge L m k 0 → ComplexMatrix2) :
    KernelMatrix (Fin 3 × PositiveEdge L m k 0) (Fin 3 × PositiveEdge L m k 0) :=
  fun ι ι' => backgroundForm L m k U (basisForm ι.1 ι.2) (basisForm ι'.1 ι'.2)
def backgroundSaddle (L m k : ℕ) (U : Edge L m k 0 → ComplexMatrix2) :
    KernelMatrix (Fin 3 × PositiveEdge L m k 0 ⊕ Fin 3 × PositiveEdge L m k k)
      (Fin 3 × PositiveEdge L m k 0 ⊕ Fin 3 × PositiveEdge L m k k) :=
  saddleMatrix (backgroundKernel L m k U) (swapKernel (iterCovariantKernel L m k U))
    (iterCovariantKernel L m k U)
def laplacianSaddle (L m k : ℕ) (U : Edge L m k 0 → ComplexMatrix2) :
    KernelMatrix (Fin 3 × Vertex L m k 0 ⊕ Fin 3 × Vertex L m k k)
      (Fin 3 × Vertex L m k 0 ⊕ Fin 3 × Vertex L m k k) :=
  saddleMatrix
    (compKernel (swapKernel (covDiffKernel L m k 0 U)) (covDiffKernel L m k 0 U))
    (swapKernel (iterAverageKernel L m k U)) (iterAverageKernel L m k U)
end FiniteSide
namespace FullSpace
section Infinite
variable {L k j : ℕ}
abbrev scaledVertexSpace (L k j : ℕ) : Submodule ℂ (Vertex L k j → ComplexMatrix2) :=
  Matrices.GroupLieProduct.tracelessFunctions (Vertex L k j)
abbrev scaledEdgeSpace (L k j : ℕ) : Submodule ℂ (PositiveEdge (meshAt L k j) → ComplexMatrix2) :=
  Matrices.GroupLieProduct.tracelessFunctions (PositiveEdge (meshAt L k j))
def scaledVertexCoboundary (l : Vertex L k j → ComplexMatrix2) : Edge L k j → ComplexMatrix2 :=
  (meshAt L k j)⁻¹ • vertexCoboundary l
def scaledEdgeCoboundary (B : Edge L k j → ComplexMatrix2) : Face L k j → ComplexMatrix2 :=
  (meshAt L k j)⁻¹ • edgeCoboundary B
def covDiffKernel (L k j : ℕ) (W : Edge L k j → ComplexMatrix2) :
    KernelMatrix (Fin 3 × Vertex L k j) (Fin 3 × PositiveEdge (meshAt L k j)) :=
  (vertexCoordinate (Vertex L k j)).kernel (edgePauliCoordinates L k j) (covDiff W)
def iterCovariantKernel (L k : ℕ) (U : Edge L k 0 → ComplexMatrix2) :
    KernelMatrix (Fin 3 × PositiveEdge (meshAt L k 0))
      (Fin 3 × PositiveEdge (meshAt L k k)) :=
  (edgePauliCoordinates L k 0).kernel (edgePauliCoordinates L k k) (iterCovariantDeriv L k U k)
def iterAverageKernel (L k : ℕ) (U : Edge L k 0 → ComplexMatrix2) :
    KernelMatrix (Fin 3 × Vertex L k 0) (Fin 3 × Vertex L k k) :=
  (vertexCoordinate (Vertex L k 0)).kernel (vertexCoordinate (Vertex L k k))
    (iterAdjointCubeAverage L k U k)
def rescaledOperators (L k : ℕ) (U : Edge L k 0 → ComplexMatrix2) :
    RescaledOperators (Vertex L k 0) (PositiveEdge (meshAt L k 0)) (Vertex L k k)
      (PositiveEdge (meshAt L k k)) where
  eta := finestMesh L k
  coarse := meshAt L k k
  D := (vertexCoordinate (Vertex L k 0)).kernel (edgePauliCoordinates L k 0)
    fun l => (finestMesh L k)⁻¹ • covDiff U l
  Q := (edgePauliCoordinates L k 0).kernel (edgePauliCoordinates L k k)
    fun B => finestMesh L k • iterCovariantDeriv L k U k B
  R := iterAverageKernel L k U
  H := fun ι ι' => (((finestMesh L k ^ 4)⁻¹ : ℝ) : ℂ) *
    complexActionHessian U (finestMesh L k • basisForm ι.1 ι.2)
      (finestMesh L k • basisForm ι'.1 ι'.2)
def covDiffTranspose (L k : ℕ) (U : Edge L k 0 → ComplexMatrix2) :
    (Edge L k 0 → ComplexMatrix2) → Vertex L k 0 → ComplexMatrix2 :=
  PairedFunctionSpace.transposeOfValues (pairedFunctions (Vertex L k 0))
    (edgePairedSpace (meshAt L k 0)) (covDiff U)
def iterAverageTranspose (L k : ℕ) (U : Edge L k 0 → ComplexMatrix2) :
    (Vertex L k k → ComplexMatrix2) → Vertex L k 0 → ComplexMatrix2 :=
  PairedFunctionSpace.transposeOfValues (pairedFunctions (Vertex L k 0))
    (pairedFunctions (Vertex L k k)) (iterAdjointCubeAverage L k U k)
def gaugeFixingTerm (L k : ℕ) (U B : Edge L k 0 → ComplexMatrix2) : Vertex L k 0 → ComplexMatrix2 :=
  covDiffTranspose L k U B -
    ((L : ℝ) ^ (4 * k)) • iterAverageTranspose L k U
      (iterAdjointCubeAverage L k U k (covDiffTranspose L k U B))
def backgroundForm (L k : ℕ) (U B B' : Edge L k 0 → ComplexMatrix2) : ℂ :=
  complexActionHessian U B B' +
    traceFinsumPairing (gaugeFixingTerm L k U B) (gaugeFixingTerm L k U B')
def backgroundKernel (L k : ℕ) (U : Edge L k 0 → ComplexMatrix2) :
    KernelMatrix (Fin 3 × PositiveEdge (meshAt L k 0))
      (Fin 3 × PositiveEdge (meshAt L k 0)) :=
  fun ι ι' => backgroundForm L k U (basisForm ι.1 ι.2) (basisForm ι'.1 ι'.2)
def backgroundSaddle (L k : ℕ) (U : Edge L k 0 → ComplexMatrix2) :
    KernelMatrix
      (Fin 3 × PositiveEdge (meshAt L k 0) ⊕ Fin 3 × PositiveEdge (meshAt L k k))
      (Fin 3 × PositiveEdge (meshAt L k 0) ⊕ Fin 3 × PositiveEdge (meshAt L k k)) :=
  saddleMatrix (backgroundKernel L k U) (swapKernel (iterCovariantKernel L k U))
    (iterCovariantKernel L k U)
def laplacianSaddle (L k : ℕ) (U : Edge L k 0 → ComplexMatrix2) :
    KernelMatrix (Fin 3 × Vertex L k 0 ⊕ Fin 3 × Vertex L k k)
      (Fin 3 × Vertex L k 0 ⊕ Fin 3 × Vertex L k k) :=
  saddleMatrix
    (compKernel (swapKernel (covDiffKernel L k 0 U)) (covDiffKernel L k 0 U))
    (swapKernel (iterAverageKernel L k U)) (iterAverageKernel L k U)
end Infinite
end FullSpace
end Tower
end YangMills.Construction
end
