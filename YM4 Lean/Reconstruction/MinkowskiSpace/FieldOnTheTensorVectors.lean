import Reconstruction.MinkowskiSpace.HilbertSpaceOfTheTensorsOfABoundedFieldForm
import Mathlib
set_option autoImplicit false
open scoped ComplexConjugate InnerProductSpace
noncomputable section
namespace YangMills.Construction.TensorFieldOperators
variable {K : Type} [NormedAddCommGroup K] [InnerProductSpace ℂ K] [CompleteSpace K]
structure FieldOperatorFacts (E : ProjectionMeasures.FourBorelSet → OneLoopNotation.BddOp K) (Ω : K)
    (A : ℝ → OneLoopNotation.BddOp K) : Prop where
  exists_unique : ∀ f : WightmanTheory.TestFn, ∃! T : FieldFormHilbert.tensorDomainIn E Ω A →ₗ[ℂ]
    FieldFormHilbert.tensorDomainIn E Ω A,
      FieldFormHilbert.IsFieldOp E Ω A (FieldFormHilbert.tensorDomainIn E Ω A) f T
  linear : ∀ (a b : ℂ) (f g h : WightmanTheory.TestFn)
    (T U V : FieldFormHilbert.tensorDomainIn E Ω A →ₗ[ℂ] FieldFormHilbert.tensorDomainIn E Ω A),
    h.1 = a • f.1 + b • g.1 → FieldFormHilbert.IsFieldOp E Ω A (FieldFormHilbert.tensorDomainIn E Ω A) f T →
    FieldFormHilbert.IsFieldOp E Ω A (FieldFormHilbert.tensorDomainIn E Ω A) g U →
    FieldFormHilbert.IsFieldOp E Ω A (FieldFormHilbert.tensorDomainIn E Ω A) h V → V = a • T + b • U
  hermitian : ∀ (f g : WightmanTheory.TestFn)
    (T U : FieldFormHilbert.tensorDomainIn E Ω A →ₗ[ℂ] FieldFormHilbert.tensorDomainIn E Ω A),
    (g.1 = fun x => conj (f.1 x)) → FieldFormHilbert.IsFieldOp E Ω A (FieldFormHilbert.tensorDomainIn E Ω A) f T →
    FieldFormHilbert.IsFieldOp E Ω A (FieldFormHilbert.tensorDomainIn E Ω A) g U →
    ∀ u v : FieldFormHilbert.tensorDomainIn E Ω A,
      ⟪(u : FieldFormHilbert.tensorHilbert E Ω A), (T v : FieldFormHilbert.tensorHilbert E Ω A)⟫_ℂ =
        ⟪(U u : FieldFormHilbert.tensorHilbert E Ω A), (v : FieldFormHilbert.tensorHilbert E Ω A)⟫_ℂ
  tempered : ∀ u v : FieldFormHilbert.tensorDomainIn E Ω A, ∃ (k : ℕ) (c : ℝ), 0 < k ∧ 0 ≤ c ∧
    ∀ (f : WightmanTheory.TestFn)
      (T : FieldFormHilbert.tensorDomainIn E Ω A →ₗ[ℂ] FieldFormHilbert.tensorDomainIn E Ω A),
      FieldFormHilbert.IsFieldOp E Ω A (FieldFormHilbert.tensorDomainIn E Ω A) f T →
      ENNReal.ofReal ‖⟪(u : FieldFormHilbert.tensorHilbert E Ω A),
          (T v : FieldFormHilbert.tensorHilbert E Ω A)⟫_ℂ‖ ≤
        ENNReal.ofReal c * WightmanTheory.schwartzNorm k f.1
  fieldWord_eq : ∀ (φ : WightmanTheory.TestFn → FieldFormHilbert.tensorDomainIn E Ω A →ₗ[ℂ]
      FieldFormHilbert.tensorDomainIn E Ω A),
    (∀ f, FieldFormHilbert.IsFieldOp E Ω A (FieldFormHilbert.tensorDomainIn E Ω A) f (φ f)) →
    ∀ (w : FieldFormHilbert.tensorDomainIn E Ω A), (((w : FieldFormHilbert.tensorHilbert E Ω A)) : K) = Ω →
    ∀ (n : ℕ) (f : Fin n → WightmanTheory.TestFn),
      ((WightmanTheory.fieldWord (fun f u => φ f u) f w : FieldFormHilbert.tensorDomainIn E Ω A) :
        FieldFormHilbert.tensorHilbert E Ω A) = FieldFormHilbert.tensorVec E Ω A f
def FieldOperatorsStatement : Prop :=
  ∀ {K : Type} [NormedAddCommGroup K] [InnerProductSpace ℂ K] [CompleteSpace K]
    (E : ProjectionMeasures.FourBorelSet → OneLoopNotation.BddOp K) (Ω : K)
    (A : ℝ → OneLoopNotation.BddOp K) (℘ C : ℝ),
    FieldForms.IsBoundedFieldForm E Ω A ℘ C → FieldOperatorFacts E Ω A
end YangMills.Construction.TensorFieldOperators
