import Reconstruction.MinkowskiSpace.HilbertSpaceOfTheTensorsOfABoundedFieldForm
import Mathlib
set_option autoImplicit false
open scoped ComplexConjugate InnerProductSpace
noncomputable section
namespace YangMills.Construction.TensorVecInner
open MinkowskiSpace FieldForms RealPointVectors WightmanTheory FieldFormHilbert ProjectionMeasures
  FormsOperators OneLoopNotation ComplexHilbert
variable {K : Type} [NormedAddCommGroup K] [InnerProductSpace ℂ K] [CompleteSpace K]
structure Conclusions (E : FourBorelSet → BddOp K) (Ω : K) (A : ℝ → BddOp K) : Prop where
  conj_mem_schwartz : ∀ f : TestFn, (fun x => conj (f.1 x)) ∈ WightmanTheory.schwartzR4
  tensorVec_fin_zero : ∀ f : Fin 0 → TestFn, (tensorVec E Ω A f : K) = Ω
  inner_tensorVec : ∀ (m' m : ℕ) (h : Fin m' → TestFn) (f : Fin m → TestFn),
    ⟪(tensorVec E Ω A h : K), (tensorVec E Ω A f : K)⟫_ℂ =
      wightmanFunctional E Ω A (m' + m)
        (tensorVal (Fin.append (fun i x => conj ((h (Fin.rev i)).1 x)) fun i => (f i).1))
  domain_eq_span : tensorDomainIn E Ω A = Submodule.span ℂ
    (Set.range fun p : Σ m : ℕ, (Fin m → TestFn) => tensorVec E Ω A p.2)
  dense_domain : Dense (tensorDomainIn E Ω A : Set (tensorHilbert E Ω A))
  eq_zero_of_inner_eq_zero : ∀ v ∈ tensorDomainIn E Ω A,
    (∀ (m : ℕ) (h : Fin m → TestFn), ⟪tensorVec E Ω A h, v⟫_ℂ = 0) → v = 0
def Claim : Prop :=
  ∀ {K : Type} [NormedAddCommGroup K] [InnerProductSpace ℂ K] [CompleteSpace K]
    (E : FourBorelSet → BddOp K) (Ω : K) (A : ℝ → BddOp K) (℘ C : ℝ),
    IsBoundedFieldForm E Ω A ℘ C → Conclusions E Ω A
end YangMills.Construction.TensorVecInner
end
