import YangMills.Construction.HilbertSpaces.CalculusOfAProjectionValuedMeasureWithBoundedFunctions
import YangMills.Construction.HilbertSpaces.FormsOperatorsAndFamiliesInAHilbertSpace
import YangMills.Construction.MinkowskiSpace.MinkowskiFormConesLorentzGroupAndEuclideanPoints
import Mathlib
set_option autoImplicit false
noncomputable section
namespace YangMills.Construction.FieldForms
variable {H : Type} [NormedAddCommGroup H] [InnerProductSpace ℂ H]
def originBorel : ProjectionMeasures.FourBorelSet := ⟨{0}, measurableSet_singleton 0⟩
def spectralTranslation [CompleteSpace H]
    (E : ProjectionMeasures.FourBorelSet → OneLoopNotation.BddOp H) (ζ : MinkowskiSpace.ComplexVec4) :
    OneLoopNotation.BddOp H :=
  PVMCalculus.pvmIntegral E
    (MinkowskiSpace.closedFutureCone.indicator fun p =>
      Complex.exp (Complex.I * MinkowskiSpace.minkowskiForm ζ (MinkowskiSpace.toComplex p)))
def imagTimeShift (a : ℝ) : MinkowskiSpace.ComplexVec4 :=
  Complex.I • MinkowskiSpace.toComplex (a • MinkowskiSpace.timeUnit)
structure IsBoundedFieldForm [CompleteSpace H]
    (E : ProjectionMeasures.FourBorelSet → OneLoopNotation.BddOp H) (Ω : H)
    (A : ℝ → OneLoopNotation.BddOp H) (p C : ℝ) : Prop where
  exponent_nonneg : 0 ≤ p
  one_le_const : 1 ≤ C
  isPVM : ProjectionMeasures.IsPVM E
  supportedOn : ProjectionMeasures.IsSupportedOn E WightmanTheory.closedFutureConeBorel
  norm_vacuum : ‖Ω‖ = 1
  origin_fixes : E originBorel Ω = Ω
  isSelfAdjoint : ∀ s : ℝ, 0 < s → HilbertToolkit.adjointOp (A s) = A s
  shift_conj : ∀ s a : ℝ, 0 < s → 0 < a →
    spectralTranslation E (imagTimeShift a) * A s * spectralTranslation E (imagTimeShift a) =
      A (s + a)
  opNorm_le : ∀ s : ℝ, 0 < s → OneLoopNotation.opNormOf (A s) ≤ C * min 1 s ^ (-p)
end YangMills.Construction.FieldForms
