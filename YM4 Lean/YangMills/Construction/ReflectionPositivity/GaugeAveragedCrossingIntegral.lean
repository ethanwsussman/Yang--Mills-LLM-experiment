import YangMills.Construction.ReflectionPositivity.CrossingWeightExpansion
import Mathlib
set_option autoImplicit false
open MeasureTheory
open scoped ComplexConjugate
noncomputable section
namespace YangMills.Construction
open Matrices ReflectionPositivity.CrossingWeight
namespace ReflectionPositivity.CrossingGaugeAverage
variable {S E : Type}
def gaugeAct (o t : E → S) (W : S → ComplexMatrix2.specialUnitary)
    (X : E → ComplexMatrix2.specialUnitary) : E → ComplexMatrix2.specialUnitary :=
  fun b => W (o b) * X b * (W (t b))⁻¹
def linkWeight [Fintype E] (β : ℝ) (X₁ X₂ : E → ComplexMatrix2.specialUnitary) : ℝ :=
  ∏ b : E, Real.exp (-β + β / 2 *
    (ComplexMatrix2.fullTrace ((X₁ b * (X₂ b)⁻¹ : ComplexMatrix2.specialUnitary) :
      ComplexMatrix2)).re)
def linkCoeff [Fintype E] (F : CharacterFamily) (β : ℝ) (γ : E → F.index) : ℝ :=
  ∏ b : E, Real.exp (-β) * F.coeff (γ b)
def linkProduct [Fintype E] (F : CharacterFamily) (γ : E → F.index)
    (X : E → ComplexMatrix2.specialUnitary) : ℂ :=
  ∏ b : E, F.fn (γ b) (X b)
def gaugeAveraged [Finite S] [Fintype E] (F : CharacterFamily) (o t : E → S) (γ : E → F.index)
    (X : E → ComplexMatrix2.specialUnitary) : ℂ :=
  ∫ W, linkProduct F γ (gaugeAct o t W X) ∂ComplexMatrix2.haarPi S
def averagedSummand [Finite S] [Fintype E] (F : CharacterFamily) (β : ℝ) (o t : E → S)
    (γ : E → F.index)
    (x : (E → ComplexMatrix2.specialUnitary) × (E → ComplexMatrix2.specialUnitary)) : ℂ :=
  (linkCoeff F β γ : ℂ) * gaugeAveraged F o t γ x.1 * conj (gaugeAveraged F o t γ x.2)
def weightIntegral [Finite S] [Fintype E] (β : ℝ) (o t : E → S)
    (x : (E → ComplexMatrix2.specialUnitary) × (E → ComplexMatrix2.specialUnitary)) : ℂ :=
  ∫ W, (linkWeight β (gaugeAct o t W x.1) x.2 : ℂ) ∂ComplexMatrix2.haarPi S
def GaugeAverageStatement : Prop :=
  ∀ (β : ℝ), 0 < β → ∀ (S E : Type) [Finite S] [Fintype E] (o t : E → S),
    (∀ γ : E → (chosenExpansion β).index, 0 ≤ linkCoeff (chosenExpansion β) β γ) ∧
    HasSum (linkCoeff (E := E) (chosenExpansion β) β)
      (Real.exp (β * (Fintype.card E : ℝ))) ∧
    (∀ γ : E → (chosenExpansion β).index,
      Continuous (gaugeAveraged (chosenExpansion β) o t γ)) ∧
    (∀ (γ : E → (chosenExpansion β).index) (X : E → ComplexMatrix2.specialUnitary),
      ‖gaugeAveraged (chosenExpansion β) o t γ X‖ ≤ 1) ∧
    (∀ X X' : E → ComplexMatrix2.specialUnitary,
      weightIntegral β o t (X, X') =
        ∫ W : S → ComplexMatrix2.specialUnitary,
          (linkWeight β (gaugeAct o t W⁻¹ X) X' : ℂ) ∂ComplexMatrix2.haarPi S) ∧
    (∀ x, HasSum (fun γ => averagedSummand (chosenExpansion β) β o t γ x)
      (weightIntegral β o t x)) ∧
    (∀ x, Summable fun γ => ‖averagedSummand (chosenExpansion β) β o t γ x‖) ∧
    HasSumUniformlyOn (averagedSummand (chosenExpansion β) β o t)
      (weightIntegral β o t) Set.univ
end ReflectionPositivity.CrossingGaugeAverage
end YangMills.Construction
end
