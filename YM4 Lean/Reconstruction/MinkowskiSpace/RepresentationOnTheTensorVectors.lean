import Reconstruction.MinkowskiSpace.EuclideanFieldFormsAndWhatAFormRepresents
import Reconstruction.MinkowskiSpace.HilbertSpaceOfTheTensorsOfABoundedFieldForm
import Mathlib
set_option autoImplicit false
noncomputable section
namespace YangMills.Construction.TensorPoincareRep
open MinkowskiSpace FieldForms RealPointVectors WightmanTheory FieldFormHilbert ProjectionMeasures
  FormsOperators OneLoopNotation ComplexHilbert
variable {K : Type} [NormedAddCommGroup K] [InnerProductSpace ℂ K] [CompleteSpace K]
structure Conclusions (E : FourBorelSet → BddOp K) (Ω : K) (A : ℝ → BddOp K) : Prop where
  act_mem_schwartz : ∀ (g : PoincareElt) (f : TestFn),
    poincareActR4 g f.1 ∈ WightmanTheory.schwartzR4
  existsUnique_op : ∀ g : PoincareElt,
    ∃! U : UnitaryMap (tensorHilbert E Ω A) (tensorHilbert E Ω A),
      IsPoincareOp E Ω A g U
  op_mul : ∀ (g₁ g₂ g₃ : PoincareElt)
    (U₁ U₂ U₃ : UnitaryMap (tensorHilbert E Ω A) (tensorHilbert E Ω A)),
    g₃.1 = poincareMul g₁.1 g₂.1 → IsPoincareOp E Ω A g₁ U₁ →
    IsPoincareOp E Ω A g₂ U₂ → IsPoincareOp E Ω A g₃ U₃ → U₃ = U₁ * U₂
  op_vacuum : ∀ (g : PoincareElt)
    (U : UnitaryMap (tensorHilbert E Ω A) (tensorHilbert E Ω A))
    (v : tensorHilbert E Ω A), IsPoincareOp E Ω A g U → (v : K) = Ω → U v = v
  op_mem_domain : ∀ (g : PoincareElt)
    (U : UnitaryMap (tensorHilbert E Ω A) (tensorHilbert E Ω A)),
    IsPoincareOp E Ω A g U → ∀ ψ ∈ tensorDomainIn E Ω A,
      U ψ ∈ tensorDomainIn E Ω A
  op_symm_mem_domain : ∀ (g : PoincareElt)
    (U : UnitaryMap (tensorHilbert E Ω A) (tensorHilbert E Ω A)),
    IsPoincareOp E Ω A g U → ∀ ψ ∈ tensorDomainIn E Ω A,
      U.symm ψ ∈ tensorDomainIn E Ω A
  op_field_covariant : ∀ (g : PoincareElt)
    (U : UnitaryMap (tensorHilbert E Ω A) (tensorHilbert E Ω A))
    (f f' : TestFn) (L L' : tensorDomainIn E Ω A →ₗ[ℂ] tensorDomainIn E Ω A),
    IsPoincareOp E Ω A g U → f'.1 = poincareActR4 g f.1 →
    IsFieldOp E Ω A (tensorDomainIn E Ω A) f L →
    IsFieldOp E Ω A (tensorDomainIn E Ω A) f' L' →
    ∀ Ψ Ψ' : tensorDomainIn E Ω A,
      (Ψ' : tensorHilbert E Ω A) = U.symm Ψ →
        U (L Ψ' : tensorHilbert E Ω A) = (L' Ψ : tensorHilbert E Ω A)
def Claim : Prop :=
  ∀ {K : Type} [NormedAddCommGroup K] [InnerProductSpace ℂ K] [CompleteSpace K]
    (E : FourBorelSet → BddOp K) (Ω : K) (A : ℝ → BddOp K) (℘ C : ℝ),
    IsBoundedFieldForm E Ω A ℘ C → IsEuclidean E Ω A → Conclusions E Ω A
end YangMills.Construction.TensorPoincareRep
end
