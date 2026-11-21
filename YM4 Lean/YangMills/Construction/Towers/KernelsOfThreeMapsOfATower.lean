import YangMills.Construction.PeriodicOperators.ProductsOfKernelsWithFiniteRows
import YangMills.Construction.Towers.CovariantLinearAverages
import Mathlib
set_option autoImplicit false
open Set
noncomputable section
namespace YangMills.Construction
namespace PeriodicOperators
section Vocabulary
variable {I J : Type}
def ColumnFinite (T : KernelMatrix I J) : Prop :=
  ∀ i : I, {j : J | T j i ≠ 0}.Finite
def Represents (T : KernelMatrix I J) (M : (I → ℂ) → J → ℂ) : Prop :=
  ∀ f : I → ℂ, ApplySummable T f ∧ applyKernel T f = M f
def kernelOfMap (M : (I → ℂ) → J → ℂ) : KernelMatrix I J :=
  Classical.epsilon fun T => Represents T M
def swapKernel (T : KernelMatrix I J) : KernelMatrix J I := fun i j => T j i
def KernelUnique (I J : Type) : Prop :=
  ∀ (M : (I → ℂ) → J → ℂ) (T T' : KernelMatrix I J), Represents T M → Represents T' M → T = T'
end Vocabulary
end PeriodicOperators
namespace Tower
open PeriodicOperators
namespace PairedFunctionSpace
def linearOfValues (S S' : PairedFunctionSpace)
    (m : (S.index → Matrices.ComplexMatrix2) → S'.index → Matrices.ComplexMatrix2) :
    S.complexSubmodule →ₗ[ℂ] S'.complexSubmodule :=
  Classical.epsilon fun T : S.complexSubmodule →ₗ[ℂ] S'.complexSubmodule =>
    ∀ f : S.complexSubmodule, (T f : S'.index → Matrices.ComplexMatrix2) = m f
def transposeOfValues (S S' : PairedFunctionSpace)
    (m : (S.index → Matrices.ComplexMatrix2) → S'.index → Matrices.ComplexMatrix2) :
    (S'.index → Matrices.ComplexMatrix2) → S.index → Matrices.ComplexMatrix2 :=
  open Classical in fun g => if h : g ∈ S'.complexSubmodule then
    (transposeMap (linearOfValues S S' m) ⟨g, h⟩ : S.complexSubmodule).1 else 0
end PairedFunctionSpace
structure PauliComponentsOfSymmetricKernel where
  space : PairedFunctionSpace
  Place : Type
  ofCoeffs : (Fin 3 × Place → ℂ) → space.index → Matrices.ComplexMatrix2
  coeffs : (space.index → Matrices.ComplexMatrix2) → Fin 3 × Place → ℂ
namespace PauliComponentsOfSymmetricKernel
abbrev Index (r : PauliComponentsOfSymmetricKernel) : Type := Fin 3 × r.Place
def mapOnCoeffs (r r' : PauliComponentsOfSymmetricKernel)
    (m : (r.space.index → Matrices.ComplexMatrix2) → r'.space.index → Matrices.ComplexMatrix2) :
    (r.Index → ℂ) → r'.Index → ℂ :=
  fun f => r'.coeffs (m (r.ofCoeffs f))
def kernel (r r' : PauliComponentsOfSymmetricKernel)
    (m : (r.space.index → Matrices.ComplexMatrix2) → r'.space.index → Matrices.ComplexMatrix2) :
    KernelMatrix r.Index r'.Index :=
  kernelOfMap (mapOnCoeffs r r' m)
def transposeOnCoeffs (r r' : PauliComponentsOfSymmetricKernel)
    (m : (r.space.index → Matrices.ComplexMatrix2) → r'.space.index → Matrices.ComplexMatrix2) :
    (r'.Index → ℂ) → r.Index → ℂ :=
  mapOnCoeffs r' r (PairedFunctionSpace.transposeOfValues r.space r'.space m)
structure HasLocalKernel (r r' : PauliComponentsOfSymmetricKernel)
    (m : (r.space.index → Matrices.ComplexMatrix2) → r'.space.index → Matrices.ComplexMatrix2) :
    Prop where
  represents : Represents (kernel r r' m) (mapOnCoeffs r r' m)
  unique : ∀ T, Represents T (mapOnCoeffs r r' m) → T = kernel r r' m
  row_finite : RowFinite (kernel r r' m)
  column_finite : ColumnFinite (kernel r r' m)
  finitely_supported : ∀ f ∈ r.space.complexSubmodule,
    r.space.IsFinitelySupported f → r'.space.IsFinitelySupported (m f)
  swap_represents : Represents (swapKernel (kernel r r' m)) (transposeOnCoeffs r r' m)
  smul_represents : ∀ z : ℂ, Represents (z • kernel r r' m) (z • mapOnCoeffs r r' m)
  smul_row_finite : ∀ z : ℂ, RowFinite (z • kernel r r' m)
  smul_column_finite : ∀ z : ℂ, ColumnFinite (z • kernel r r' m)
  smul_swap_represents : ∀ z : ℂ,
    Represents (z • swapKernel (kernel r r' m)) (z • transposeOnCoeffs r r' m)
  smul_swap_row_finite : ∀ z : ℂ,
    RowFinite (z • swapKernel (kernel r r' m))
  smul_swap_column_finite : ∀ z : ℂ,
    ColumnFinite (z • swapKernel (kernel r r' m))
end PauliComponentsOfSymmetricKernel
def vertexCoordinate (V : Type) : PauliComponentsOfSymmetricKernel where
  space := pairedFunctions V
  Place := V
  ofCoeffs := ofPauliCoeffs
  coeffs := toPauliCoeffs
def edgePauliCoordinates (L n k j : ℕ) : PauliComponentsOfSymmetricKernel where
  space := edgePairedSpace L n k j
  Place := PositiveEdge L n k j
  ofCoeffs := fun c => open Classical in
    extendOddly fun b => if h : b.IsPositivelyOriented then ofPauliCoeffs c ⟨b, h⟩ else 0
  coeffs := fun B => toPauliCoeffs (restrictToPositiveEdges B)
def FullSpace.edgePauliCoordinates (L k j : ℕ) : PauliComponentsOfSymmetricKernel where
  space := FullSpace.edgePairedSpace (meshAt L k j)
  Place := FullSpace.PositiveEdge (meshAt L k j)
  ofCoeffs := fun c => open Classical in
    FullSpace.extendOddly fun b =>
      if h : b.IsPositivelyOriented then ofPauliCoeffs c ⟨b, h⟩ else 0
  coeffs := fun B => toPauliCoeffs (FullSpace.restrictToPositiveEdges B)
namespace ThreeMapKernels
def OnTorus (L n k : ℕ) : Prop :=
  (∀ i j : ℕ, i ≤ k → j ≤ k →
    KernelUnique (vertexCoordinate (Vertex L n k i)).Index (vertexCoordinate (Vertex L n k j)).Index ∧
    KernelUnique (vertexCoordinate (Vertex L n k i)).Index (edgePauliCoordinates L n k j).Index ∧
    KernelUnique (edgePauliCoordinates L n k i).Index (vertexCoordinate (Vertex L n k j)).Index ∧
    KernelUnique (edgePauliCoordinates L n k i).Index (edgePauliCoordinates L n k j).Index) ∧
  (∀ W ∈ fieldsIn L n k 0 PeriodicLattice.complexGaugeGroup,
    PauliComponentsOfSymmetricKernel.HasLocalKernel (vertexCoordinate (Vertex L n k 0))
      (edgePauliCoordinates L n k 0) (covDiff W)) ∧
  (∀ W ∈ fieldsIn L n k k PeriodicLattice.complexGaugeGroup,
    PauliComponentsOfSymmetricKernel.HasLocalKernel (vertexCoordinate (Vertex L n k k))
      (edgePauliCoordinates L n k k) (covDiff W)) ∧
  ∀ U ∈ smallIterateFields L n k,
    PauliComponentsOfSymmetricKernel.HasLocalKernel (edgePauliCoordinates L n k 0) (edgePauliCoordinates L n k k)
      (iterCovariantDeriv L n k U k) ∧
    PauliComponentsOfSymmetricKernel.HasLocalKernel (vertexCoordinate (Vertex L n k 0))
      (vertexCoordinate (Vertex L n k k)) (iterAdjointCubeAverage L n k U k)
def OnFullSpace (L k : ℕ) : Prop :=
  (∀ i j : ℕ, i ≤ k → j ≤ k →
    KernelUnique (vertexCoordinate (FullSpace.Vertex L k i)).Index
      (vertexCoordinate (FullSpace.Vertex L k j)).Index ∧
    KernelUnique (vertexCoordinate (FullSpace.Vertex L k i)).Index
      (FullSpace.edgePauliCoordinates L k j).Index ∧
    KernelUnique (FullSpace.edgePauliCoordinates L k i).Index
      (vertexCoordinate (FullSpace.Vertex L k j)).Index ∧
    KernelUnique (FullSpace.edgePauliCoordinates L k i).Index (FullSpace.edgePauliCoordinates L k j).Index) ∧
  (∀ W ∈ FullSpace.fieldsValuedIn L k 0 PeriodicLattice.complexGaugeGroup,
    PauliComponentsOfSymmetricKernel.HasLocalKernel (vertexCoordinate (FullSpace.Vertex L k 0))
      (FullSpace.edgePauliCoordinates L k 0) (FullSpace.covDiff W)) ∧
  (∀ W ∈ FullSpace.fieldsValuedIn L k k PeriodicLattice.complexGaugeGroup,
    PauliComponentsOfSymmetricKernel.HasLocalKernel (vertexCoordinate (FullSpace.Vertex L k k))
      (FullSpace.edgePauliCoordinates L k k) (FullSpace.covDiff W)) ∧
  ∀ U ∈ FullSpace.smallIterateFields L k,
    PauliComponentsOfSymmetricKernel.HasLocalKernel (FullSpace.edgePauliCoordinates L k 0)
      (FullSpace.edgePauliCoordinates L k k) (FullSpace.iterCovariantDeriv L k U k) ∧
    PauliComponentsOfSymmetricKernel.HasLocalKernel (vertexCoordinate (FullSpace.Vertex L k 0))
      (vertexCoordinate (FullSpace.Vertex L k k)) (FullSpace.iterAdjointCubeAverage L k U k)
def Claim : Prop :=
  ∀ L : ℕ, Conventions.IsAdmissibleBlockingFactor L → ∀ k : ℕ, 1 ≤ k →
    (∀ n : ℕ, 0 < n → OnTorus L n k) ∧ OnFullSpace L k
end ThreeMapKernels
end Tower
end YangMills.Construction
end
