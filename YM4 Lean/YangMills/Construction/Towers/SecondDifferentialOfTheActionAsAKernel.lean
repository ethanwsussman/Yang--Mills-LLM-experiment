import YangMills.Construction.Towers.TheHolomorphicActionOfATower
import Mathlib
set_option autoImplicit false
namespace YangMills.Construction
open Set
noncomputable section
namespace Tower
namespace HessianKernel
open PeriodicOperators (KernelMatrix ApplySummableAt)
section Predicates
variable {α σ : Type}
def IsSymmBilinearOn (𝒮 : Set (α → Matrices.ComplexMatrix2))
    (Q : (α → Matrices.ComplexMatrix2) → (α → Matrices.ComplexMatrix2) → ℂ) : Prop :=
  ∀ z : ℂ, ∀ E₁ ∈ 𝒮, ∀ E₂ ∈ 𝒮, ∀ E₃ ∈ 𝒮,
    Q (z • E₁ + E₂) E₃ = z * Q E₁ E₃ + Q E₂ E₃ ∧
      Q E₃ (z • E₁ + E₂) = z * Q E₃ E₁ + Q E₃ E₂ ∧
      Q E₁ E₃ = Q E₃ E₁
def SupportedOnRelation (T : KernelMatrix (Fin 3 × σ) (Fin 3 × σ)) (R : σ → σ → Prop) : Prop :=
  ∀ ι ι' : Fin 3 × σ, ¬ R ι.2 ι'.2 → T ι ι' = 0
def RowFinite (T : KernelMatrix (Fin 3 × σ) (Fin 3 × σ)) : Prop :=
  ∀ ι : Fin 3 × σ, {ι' : Fin 3 × σ | T ι ι' ≠ 0}.Finite
def IsSymm (T : KernelMatrix (Fin 3 × σ) (Fin 3 × σ)) : Prop :=
  ∀ ι ι' : Fin 3 × σ, T ι ι' = T ι' ι
end Predicates
def HoldsOnTorus (L n k j : ℕ) : Prop :=
  ∀ U ∈ fieldsIn L n k j PeriodicLattice.complexGaugeGroup,
    IsSymmBilinearOn (complexEdgeForms L n k j : Set (Edge L n k j → Matrices.ComplexMatrix2))
      (complexActionHessian U) ∧
    SupportedOnRelation (complexHessianKernel U)
      (fun b b' : PositiveEdge L n k j =>
        ∃ p : Face L n k j, b.1 ∈ faceEdges p ∧ b'.1 ∈ faceEdges p) ∧
    RowFinite (complexHessianKernel U) ∧
    (∀ B ∈ complexEdgeForms L n k j, ∀ ι,
      ApplySummableAt (complexHessianKernel U) (toPauliCoeffs (restrictToPositiveEdges B)) ι) ∧
    (∀ B ∈ complexEdgeForms L n k j, ∀ B' ∈ complexEdgeForms L n k j,
      edgeFormPairing B (complexHessianOperator U B') = complexActionHessian U B B') ∧
    IsSymm (complexHessianKernel U)
def finiteSupportComplexForms (L k j : ℕ) : Set (FullSpace.Edge L k j → Matrices.ComplexMatrix2) :=
  {B | B ∈ FullSpace.complexEdgeForms (meshAt L k j) ∧ FullSpace.HasFiniteEdgeSupport B}
def HoldsOnFullSpace (L k j : ℕ) : Prop :=
  ∀ U ∈ FullSpace.fieldsValuedIn L k j PeriodicLattice.complexGaugeGroup,
    IsSymmBilinearOn (finiteSupportComplexForms L k j)
      (FullSpace.complexActionHessian U) ∧
    SupportedOnRelation (FullSpace.complexHessianKernel U)
      (fun b b' : FullSpace.PositiveEdge (meshAt L k j) =>
        ∃ p : FullSpace.Face L k j,
          b.1 ∈ FullSpace.faceEdges p ∧ b'.1 ∈ FullSpace.faceEdges p) ∧
    RowFinite (FullSpace.complexHessianKernel U) ∧
    (∀ B ∈ FullSpace.complexEdgeForms (meshAt L k j), ∀ ι,
      ApplySummableAt (FullSpace.complexHessianKernel U)
        (toPauliCoeffs (FullSpace.restrictToPositiveEdges B)) ι) ∧
    (∀ B ∈ finiteSupportComplexForms L k j, ∀ B' ∈ finiteSupportComplexForms L k j,
      FullSpace.finiteEdgePairing B (FullSpace.complexHessianOperator U B') =
        FullSpace.complexActionHessian U B B') ∧
    IsSymm (FullSpace.complexHessianKernel U)
def KernelProperties : Prop :=
  ∀ L : ℕ, Conventions.IsAdmissibleBlockingFactor L → ∀ k j : ℕ, j ≤ k →
    (∀ n : ℕ, 0 < n → HoldsOnTorus L n k j) ∧ HoldsOnFullSpace L k j
end HessianKernel
end Tower
end
end YangMills.Construction
