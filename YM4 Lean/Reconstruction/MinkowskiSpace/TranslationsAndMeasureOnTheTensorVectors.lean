import Reconstruction.MinkowskiSpace.HilbertSpaceOfTheTensorsOfABoundedFieldForm
import Mathlib
set_option autoImplicit false
noncomputable section
namespace YangMills.Construction.TensorTranslations
open MinkowskiSpace FieldForms WightmanTheory FieldFormHilbert ProjectionMeasures FormsOperators
  OneLoopNotation PVMCalculus
variable {K : Type} [NormedAddCommGroup K] [InnerProductSpace ℂ K] [CompleteSpace K]
structure Properties (E : FourBorelSet → BddOp K) (Ω : K) (A : ℝ → BddOp K) : Prop where
  translation_eq : ∀ (a : RealVec4)
    (U : UnitaryMap (tensorHilbert E Ω A) (tensorHilbert E Ω A)),
    IsPoincareOp E Ω A (pureTranslation a) U → ∀ v : tensorHilbert E Ω A,
      ((U v : tensorHilbert E Ω A) : K) = spectralTranslation E (toComplex a) v
  exists_restriction : ∃ F : FourBorelSet → BddOp (tensorHilbert E Ω A),
    IsMeasureRestriction E Ω A F ∧ IsPVM F ∧
      IsSupportedOn F closedFutureConeBorel ∧
      (∀ (a : RealVec4) (V : BddOp (tensorHilbert E Ω A)),
        (∀ v : tensorHilbert E Ω A,
          ((V v : tensorHilbert E Ω A) : K) = spectralTranslation E (toComplex a) v) →
        HasWeakIntegrals F (minkowskiPhase a) V) ∧
      ∀ t : ℝ, 0 ≤ t → ∀ v : tensorHilbert E Ω A,
        ((HermitianScalarTheory.hamiltonianSemigroup F t v : tensorHilbert E Ω A) : K) =
          spectralTranslation E (imagTimeShift t) v
def Holds : Prop :=
  ∀ {K : Type} [NormedAddCommGroup K] [InnerProductSpace ℂ K] [CompleteSpace K]
    (E : FourBorelSet → BddOp K) (Ω : K) (A : ℝ → BddOp K) (℘ C : ℝ),
    IsBoundedFieldForm E Ω A ℘ C → Properties E Ω A
end YangMills.Construction.TensorTranslations
end
