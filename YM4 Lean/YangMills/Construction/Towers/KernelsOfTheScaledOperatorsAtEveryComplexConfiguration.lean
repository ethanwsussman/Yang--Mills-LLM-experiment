import YangMills.Construction.Towers.TheScaledPicture
import Mathlib
set_option autoImplicit false
open Set
noncomputable section
namespace YangMills.Construction.Tower.RescaledKernels
open PeriodicOperators (KernelMatrix compKernel Represents RowFinite ColumnFinite
  ApplySummable CompSummable)
def CompSumsFinite {N N' N'' : Type} (T : KernelMatrix N' N'') (S : KernelMatrix N N') :
    Prop :=
  ∀ (ι'' : N'') (ι : N), {κ : N' | T ι'' κ * S κ ι ≠ 0}.Finite
structure KernelsWellFormed {S₀ B₀ S B : Type} (p : RescaledOperators S₀ B₀ S B)
    (Dm : (Fin 3 × S₀ → ℂ) → Fin 3 × B₀ → ℂ) (src tgt : B₀ → S₀)
    (vertexFns : Set (S₀ → Matrices.ComplexMatrix2))
    (edgeFns : Set (B₀ → Matrices.ComplexMatrix2)) : Prop where
  represents : Represents p.D Dm
  D_eq_zero : ∀ (a' : Fin 3) (b : B₀) (a : Fin 3) (x : S₀), x ≠ src b → x ≠ tgt b →
    p.D (a', b) (a, x) = 0
  D_rowFinite : RowFinite p.D
  D_columnFinite : ColumnFinite p.D
  H_rowFinite : RowFinite p.H
  H_columnFinite : ColumnFinite p.H
  D_Dt_sumsFinite : CompSumsFinite p.D p.Dt
  Dt_D_sumsFinite : CompSumsFinite p.Dt p.D
  D_Dt_summable : CompSummable p.D p.Dt
  Dt_D_summable : CompSummable p.Dt p.D
  K_rowFinite : RowFinite p.K
  K_columnFinite : ColumnFinite p.K
  Delta_rowFinite : RowFinite p.Delta
  Delta_columnFinite : ColumnFinite p.Delta
  K_applySummable : ∀ f ∈ edgeFns, ApplySummable p.K (toPauliCoeffs f)
  Delta_applySummable : ∀ f ∈ vertexFns, ApplySummable p.Delta (toPauliCoeffs f)
def OnTorus (L n k : ℕ) : Prop :=
  ∀ U ∈ fieldsIn L n k 0 PeriodicLattice.complexGaugeGroup,
    KernelsWellFormed (rescaledOperators L n k U)
      ((vertexCoordinate (Vertex L n k 0)).mapOnCoeffs (edgePauliCoordinates L n k 0)
        fun l => (finestMesh L k)⁻¹ • covDiff U l)
      (fun b => b.1.source) (fun b => b.1.target)
      (scaledVertexSpace L n k 0 : Set (Vertex L n k 0 → Matrices.ComplexMatrix2))
      (scaledEdgeSpace L n k 0 : Set (PositiveEdge L n k 0 → Matrices.ComplexMatrix2))
def OnFullSpace (L k : ℕ) : Prop :=
  ∀ U ∈ FullSpace.fieldsValuedIn L k 0 PeriodicLattice.complexGaugeGroup,
    KernelsWellFormed (FullSpace.rescaledOperators L k U)
      ((vertexCoordinate (FullSpace.Vertex L k 0)).mapOnCoeffs (FullSpace.edgePauliCoordinates L k 0)
        fun l => (finestMesh L k)⁻¹ • FullSpace.covDiff U l)
      (fun b => b.1.initial) (fun b => b.1.terminal)
      (FullSpace.scaledVertexSpace L k 0 :
        Set (FullSpace.Vertex L k 0 → Matrices.ComplexMatrix2))
      (FullSpace.scaledEdgeSpace L k 0 :
        Set (FullSpace.PositiveEdge (meshAt L k 0) → Matrices.ComplexMatrix2))
def KernelsWellFormedEverywhere : Prop :=
  ∀ L : ℕ, Conventions.IsAdmissibleBlockingFactor L → ∀ k : ℕ, 1 ≤ k →
    (∀ n : ℕ, 0 < n → OnTorus L n k) ∧ OnFullSpace L k
end YangMills.Construction.Tower.RescaledKernels
end
