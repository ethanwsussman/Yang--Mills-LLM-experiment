import YangMills.Construction.Matrices.FunctionsAndOperatorsOfSeveralVariablesOnG
import Mathlib
set_option autoImplicit false
open MeasureTheory YangMills.Construction.SpinHarmonics YangMills.Construction.Matrices
noncomputable section
namespace YangMills.Construction.TransferOperators
variable {J V : Type}
def twistedConjAction (t h : J → V) (g : V → ComplexMatrix2.specialUnitary)
    (u : J → ComplexMatrix2.specialUnitary) : J → ComplexMatrix2.specialUnitary :=
  fun e => g (t e) * u e * (g (h e))⁻¹
def IsTwistedTranslation [Countable J] (t h : J → V) (g : V → ComplexMatrix2.specialUnitary)
    (T : HaarL2 J →L[ℂ] HaarL2 J) : Prop :=
  ∀ φ : HaarL2 J, (T φ : (J → ComplexMatrix2.specialUnitary) → ℂ) =ᵐ[ComplexMatrix2.haarPi J]
    fun u => (φ : (J → ComplexMatrix2.specialUnitary) → ℂ) (twistedConjAction t h g⁻¹ u)
def IsTwistedAverage [Countable J] [Countable V] (t h : J → V)
    (T : HaarL2 J →L[ℂ] HaarL2 J) : Prop :=
  ∀ φ : HaarL2 J, (T φ : (J → ComplexMatrix2.specialUnitary) → ℂ) =ᵐ[ComplexMatrix2.haarPi J]
    fun u => ∫ g, (φ : (J → ComplexMatrix2.specialUnitary) → ℂ) (twistedConjAction t h g⁻¹ u)
      ∂ComplexMatrix2.haarPi V
end YangMills.Construction.TransferOperators
end
