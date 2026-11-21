import Reconstruction.MinkowskiSpace.HilbertSpaceOfTheTensorsOfABoundedFieldForm
import Mathlib
set_option autoImplicit false
noncomputable section
namespace YangMills.Construction.TensorHilbertSeparable
open MinkowskiSpace FieldForms RealPointVectors WightmanTheory FieldFormHilbert ProjectionMeasures
  FormsOperators OneLoopNotation ComplexHilbert
variable {K : Type} [NormedAddCommGroup K] [InnerProductSpace ℂ K] [CompleteSpace K]
structure Conclusions (E : FourBorelSet → BddOp K) (Ω : K) (A : ℝ → BddOp K) : Prop where
  separableSpace : TopologicalSpace.SeparableSpace (tensorHilbert E Ω A)
  translation_invariant_eq_smul : (∀ χ : K,
      (∀ t : ℝ, 0 ≤ t → spectralTranslation E (imagTimeShift t) χ = χ) → ∃ c : ℂ, χ = c • Ω) →
    ∀ ψ : tensorHilbert E Ω A,
      (∀ a : RealVec4, spectralTranslation E (toComplex a) (ψ : K) = ψ) → ∃ c : ℂ, (ψ : K) = c • Ω
def Claim : Prop :=
  ∀ {K : Type} [NormedAddCommGroup K] [InnerProductSpace ℂ K] [CompleteSpace K]
    (E : FourBorelSet → BddOp K) (Ω : K) (A : ℝ → BddOp K) (℘ C : ℝ),
    IsBoundedFieldForm E Ω A ℘ C → Conclusions E Ω A
end YangMills.Construction.TensorHilbertSeparable
end
