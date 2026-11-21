import YangMills.Construction.Towers.KernelsOfThreeMapsOfATower
import Mathlib
set_option autoImplicit false
open Set
open YangMills.Construction.Matrices (ComplexMatrix2)
noncomputable section
namespace YangMills.Construction.Tower
namespace CovDiffTransposes
open YangMills.Construction.PeriodicOperators (KernelMatrix ApplySummableAt applyKernel compKernel
  RowFinite ColumnFinite swapKernel colourVertices colourEdges colourFaces)
open YangMills.Construction.Tower.PairedFunctionSpace (linearOfValues transposeOfValues)
section
def matrixKernel (r r' : PauliComponentsOfSymmetricKernel)
    (m : (r.space.index → ComplexMatrix2) → r'.space.index → ComplexMatrix2) :
    KernelMatrix r.Index r'.Index :=
  open Classical in fun ι' ι => r'.coeffs (m (r.ofCoeffs fun κ => if κ = ι then 1 else 0)) ι'
def IsRepresentedBy (r r' : PauliComponentsOfSymmetricKernel)
    (M : (r.space.index → ComplexMatrix2) → r'.space.index → ComplexMatrix2)
    (K : KernelMatrix r.Index r'.Index) : Prop :=
  ∀ f ∈ r.space.complexSubmodule, ∀ κ' : r'.Index,
    {κ : r.Index | K κ' κ * r.coeffs f κ ≠ 0}.Finite ∧
      r'.coeffs (M f) κ' = applyKernel K (r.coeffs f) κ'
def IsRepresentedByComp (r r' r'' : PauliComponentsOfSymmetricKernel)
    (M : (r.space.index → ComplexMatrix2) → r''.space.index → ComplexMatrix2)
    (K : KernelMatrix r'.Index r''.Index) (K' : KernelMatrix r.Index r'.Index) : Prop :=
  (∀ (κ'' : r''.Index) (κ : r.Index), {κ' : r'.Index | K κ'' κ' * K' κ' κ ≠ 0}.Finite) ∧
    IsRepresentedBy r r'' M (compKernel K K')
def transposeComp (r r' : PauliComponentsOfSymmetricKernel)
    (m : (r.space.index → ComplexMatrix2) → r'.space.index → ComplexMatrix2) :
    (r.space.index → ComplexMatrix2) → r.space.index → ComplexMatrix2 :=
  fun f => transposeOfValues r.space r'.space m (m f)
def compTranspose (r r' : PauliComponentsOfSymmetricKernel)
    (m : (r.space.index → ComplexMatrix2) → r'.space.index → ComplexMatrix2) :
    (r'.space.index → ComplexMatrix2) → r'.space.index → ComplexMatrix2 :=
  fun g => m (transposeOfValues r.space r'.space m g)
structure HasTransposeKernel (r r' : PauliComponentsOfSymmetricKernel)
    (m : (r.space.index → ComplexMatrix2) → r'.space.index → ComplexMatrix2) : Prop where
  coe_linear : ∀ f : r.space.complexSubmodule,
    (linearOfValues r.space r'.space m f : r'.space.index → ComplexMatrix2) = m f
  preserves_finite_support :
    PairedFunctionSpace.PreservesFiniteSupport (linearOfValues r.space r'.space m)
  isTranspose : PairedFunctionSpace.IsTransposeMap (linearOfValues r.space r'.space m)
    (PairedFunctionSpace.transposeMap (linearOfValues r.space r'.space m))
  row_finite : RowFinite (matrixKernel r r' m)
  column_finite : ColumnFinite (matrixKernel r r' m)
  represents : IsRepresentedBy r r' m (matrixKernel r r' m)
  transpose_represents : IsRepresentedBy r' r (transposeOfValues r.space r'.space m)
    (swapKernel (matrixKernel r r' m))
structure LatticeTransposeData (rs rb rp : PauliComponentsOfSymmetricKernel)
    (D d₀ : (rs.space.index → ComplexMatrix2) → rb.space.index → ComplexMatrix2)
    (d₁ : (rb.space.index → ComplexMatrix2) → rp.space.index → ComplexMatrix2)
    (A : (rb.space.index → ComplexMatrix2) → rb.space.index → ComplexMatrix2)
    (K : KernelMatrix rb.Index rb.Index) : Prop where
  covDiff : HasTransposeKernel rs rb D
  vertexCoboundary : HasTransposeKernel rs rb d₀
  edgeCoboundary : HasTransposeKernel rb rp d₁
  transposeComp_mem : ∀ l ∈ rs.space.complexSubmodule,
    D l ∈ rb.space.complexSubmodule ∧ transposeComp rs rb D l ∈ rs.space.complexSubmodule
  compTranspose_mem : ∀ B ∈ rb.space.complexSubmodule,
    transposeOfValues rs.space rb.space D B ∈ rs.space.complexSubmodule ∧
      compTranspose rs rb D B ∈ rb.space.complexSubmodule
  operator_mem : ∀ B ∈ rb.space.complexSubmodule,
    (∀ ι, ApplySummableAt K (rb.coeffs B) ι) ∧
      A B ∈ rb.space.complexSubmodule ∧
        A B + compTranspose rs rb D B ∈ rb.space.complexSubmodule
  transposeComp_represents : IsRepresentedByComp rs rb rs (transposeComp rs rb D)
    (swapKernel (matrixKernel rs rb D)) (matrixKernel rs rb D)
  compTranspose_represents : IsRepresentedByComp rb rs rb (compTranspose rs rb D)
    (matrixKernel rs rb D) (swapKernel (matrixKernel rs rb D))
end
def OnTorus (L n k j : ℕ) : Prop :=
  ∀ U ∈ fieldsIn L n k j PeriodicLattice.complexGaugeGroup,
    LatticeTransposeData (vertexCoordinate (Vertex L n k j)) (edgePauliCoordinates L n k j)
      (vertexCoordinate (Face L n k j)) (covDiff U) vertexCoboundary edgeCoboundary
      (complexHessianOperator U) (complexHessianKernel U)
def OnFullSpace (L k j : ℕ) : Prop :=
  ∀ U ∈ FullSpace.fieldsValuedIn L k j PeriodicLattice.complexGaugeGroup,
    LatticeTransposeData (vertexCoordinate (FullSpace.Vertex L k j)) (FullSpace.edgePauliCoordinates L k j)
      (vertexCoordinate (FullSpace.Face L k j)) (FullSpace.covDiff U)
      FullSpace.vertexCoboundary FullSpace.edgeCoboundary
      (FullSpace.complexHessianOperator U) (FullSpace.complexHessianKernel U) ∧
    PeriodicOperators.wTranspose (colourVertices L k j).weightOf (colourEdges L k j).weightOf
        (matrixKernel (vertexCoordinate (FullSpace.Vertex L k j)) (FullSpace.edgePauliCoordinates L k j)
          (FullSpace.covDiff U)) =
      swapKernel (matrixKernel (vertexCoordinate (FullSpace.Vertex L k j))
        (FullSpace.edgePauliCoordinates L k j) (FullSpace.covDiff U)) ∧
    PeriodicOperators.wTranspose (colourVertices L k j).weightOf (colourEdges L k j).weightOf
        (matrixKernel (vertexCoordinate (FullSpace.Vertex L k j)) (FullSpace.edgePauliCoordinates L k j)
          FullSpace.vertexCoboundary) =
      swapKernel (matrixKernel (vertexCoordinate (FullSpace.Vertex L k j))
        (FullSpace.edgePauliCoordinates L k j) FullSpace.vertexCoboundary) ∧
    PeriodicOperators.wTranspose (colourEdges L k j).weightOf (colourFaces L k j).weightOf
        (matrixKernel (FullSpace.edgePauliCoordinates L k j) (vertexCoordinate (FullSpace.Face L k j))
          FullSpace.edgeCoboundary) =
      swapKernel (matrixKernel (FullSpace.edgePauliCoordinates L k j)
        (vertexCoordinate (FullSpace.Face L k j)) FullSpace.edgeCoboundary)
def Claim : Prop :=
  ∀ L : ℕ, Conventions.IsAdmissibleBlockingFactor L → ∀ k j : ℕ, j ≤ k →
    (∀ n : ℕ, 0 < n → OnTorus L n k j) ∧ OnFullSpace L k j
end CovDiffTransposes
end YangMills.Construction.Tower
end
