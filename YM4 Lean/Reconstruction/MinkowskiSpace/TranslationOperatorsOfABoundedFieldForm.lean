import YangMills.Construction.Coordinates.HolomorphyInCoordinates
import YangMills.Construction.MinkowskiSpace.BoundedFieldForms
import Mathlib
set_option autoImplicit false
noncomputable section
namespace YangMills.Construction.FieldFormTranslations
open scoped InnerProductSpace
variable {K : Type} [NormedAddCommGroup K] [InnerProductSpace ℂ K] [CompleteSpace K]
def complexEucNorm (ζ : MinkowskiSpace.ComplexVec4) : ℝ := Real.sqrt (∑ μ, ‖ζ μ‖ ^ 2)
def ImInClosedCone (ζ : MinkowskiSpace.ComplexVec4) : Prop :=
  MinkowskiSpace.imPart ζ ∈ MinkowskiSpace.closedFutureCone
def IsContractionSemigroup
    (E : ProjectionMeasures.FourBorelSet → OneLoopNotation.BddOp K) (Ω : K) : Prop :=
  (∀ ζ ζ' : MinkowskiSpace.ComplexVec4, ImInClosedCone ζ → ImInClosedCone ζ' →
    OneLoopNotation.opNormOf (FieldForms.spectralTranslation E ζ) ≤ 1 ∧
    FieldForms.spectralTranslation E ζ * FieldForms.spectralTranslation E ζ' =
      FieldForms.spectralTranslation E (ζ + ζ') ∧
    HilbertToolkit.adjointOp (FieldForms.spectralTranslation E ζ) =
      FieldForms.spectralTranslation E (-MinkowskiSpace.conjPoint ζ) ∧
    FieldForms.spectralTranslation E 0 = ComplexHilbert.idOp K ∧
    FieldForms.spectralTranslation E ζ Ω = Ω) ∧
  (∀ a : MinkowskiSpace.RealVec4, ComplexHilbert.IsUnitaryMap
    (FieldForms.spectralTranslation E (MinkowskiSpace.toComplex a) : K →ₗ[ℂ] K)) ∧
  SesquilinearForms.StronglyContinuous fun a : MinkowskiSpace.RealVec4 =>
    FieldForms.spectralTranslation E (MinkowskiSpace.toComplex a)
def LipschitzInTube (E : ProjectionMeasures.FourBorelSet → OneLoopNotation.BddOp K) : Prop :=
  ∀ (ζ ζ' : MinkowskiSpace.ComplexVec4) (ε : ℝ), ImInClosedCone ζ →
    ImInClosedCone ζ' → 0 < ε → MinkowskiSpace.tubeGap ζ ≥ ε → MinkowskiSpace.tubeGap ζ' ≥ ε →
    OneLoopNotation.opNormOf
        (FieldForms.spectralTranslation E ζ - FieldForms.spectralTranslation E ζ') ≤
      ε⁻¹ * complexEucNorm (ζ - ζ')
def HolomorphicMatrixCoeffs (E : ProjectionMeasures.FourBorelSet → OneLoopNotation.BddOp K) :
    Prop :=
  ∀ χ χ' : K, Coordinates.ComplexCoordinates.IsHolomorphicIn (N' := 1) MinkowskiSpace.futureTube
    fun ζ _ => ⟪χ, FieldForms.spectralTranslation E ζ χ'⟫_ℂ
def TranslationOperatorFacts : Prop :=
  ∀ (K : Type) [NormedAddCommGroup K] [InnerProductSpace ℂ K] [CompleteSpace K]
    (E : ProjectionMeasures.FourBorelSet → OneLoopNotation.BddOp K) (Ω : K)
    (A : ℝ → OneLoopNotation.BddOp K) (P C : ℝ),
    FieldForms.IsBoundedFieldForm E Ω A P C →
      IsContractionSemigroup E Ω ∧ LipschitzInTube E ∧ HolomorphicMatrixCoeffs E
end YangMills.Construction.FieldFormTranslations
