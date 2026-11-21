import YangMills.Construction.InfiniteLattice.ModifiedBesselFunctionsAndCharacterCoefficients
import YangMills.Construction.Matrices.FunctionsAndOperatorsOfSeveralVariablesOnG
import Mathlib
set_option autoImplicit false
open MeasureTheory YangMills.Construction.SpinHarmonics YangMills.Construction.Matrices
noncomputable section
namespace YangMills.Construction.TransferOperators
section Coefficients
variable (β : ℝ) {B : Type} [Finite B]
def charCoeffProd (l : B → HalfNatural) : ℂ := ∏ᶠ b, weightCharCoeff β (l b)
def peterWeylCoeff (α : PeterWeylIndex B) : ℂ := charCoeffProd β (spins α)
def sqrtCharCoeffProd (l : B → HalfNatural) : ℝ := Real.sqrt (charCoeffProd β l).re
def invSqrtCharCoeffProd (l : B → HalfNatural) : ℝ := (sqrtCharCoeffProd β l)⁻¹
def sqrtPeterWeylCoeff (α : PeterWeylIndex B) : ℝ := Real.sqrt (peterWeylCoeff β α).re
end Coefficients
def sqrtCharCoeff (β : ℝ) (l : HalfNatural) : ℝ := Real.sqrt (weightCharCoeff β l).re
def sqrtKernel (β : ℝ) (g g' : ComplexMatrix2.specialUnitary) : ℂ :=
  ∑' l : HalfNatural, (sqrtCharCoeff β l : ℂ) * ((2 * l.toReal + 1 : ℝ) : ℂ) *
    spinCharacter l (g * g'⁻¹)
def sqrtOperator (β : ℝ) :
    Lp ℂ 2 ComplexMatrix2.haarProb →L[ℂ] Lp ℂ 2 ComplexMatrix2.haarProb :=
  Schatten.kernelOp ComplexMatrix2.haarProb fun q => sqrtKernel β q.1 q.2
def sqrtLinkKernel (β : ℝ) {B : Type} (u u' : B → ComplexMatrix2.specialUnitary) : ℂ :=
  ∏ᶠ b, sqrtKernel β (u b) (u' b)
def sqrtLinkOperator (β : ℝ) (B : Type) [Finite B] : HaarL2 B →L[ℂ] HaarL2 B :=
  Schatten.kernelOp (ComplexMatrix2.haarPi B) fun q => sqrtLinkKernel β q.1 q.2
def truncInvSqrtLinkOperator (β : ℝ) (B : Type) [Finite B] (κ : HalfNatural) :
    HaarL2 B →L[ℂ] HaarL2 B :=
  ∑ l ∈ boundedWeights B κ, (invSqrtCharCoeffProd β l : ℂ) • isotypicProj l
end YangMills.Construction.TransferOperators
end
