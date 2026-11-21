import YangMills.Construction.EuclideanBorel.RepresentationSpectralMeasure
import YangMills.Construction.HilbertSpaces.FormsOperatorsAndFamiliesInAHilbertSpace
import YangMills.Construction.SpectralMeasures.DeterminingFamilies
import Mathlib
set_option autoImplicit false
noncomputable section
namespace YangMills.Construction.EuclideanBorel
open YangMills.Construction.FormsOperators (Commutes UnitaryMap)
section UnitarySpectral
variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
def IsUnitarySpectralMeasure (U : UnitaryMap H H)
    (E : BorelSubset 2 → H →L[ℂ] H) : Prop :=
  IsPVM E ∧ IsSupportedOnPVM E planeUnitCircleBorel ∧
    ∀ k : ℤ, SpectralIntegralIs E (circleChar k) ⇑(U ^ k : UnitaryMap H H)
def unitarySpectralMeasure (U : UnitaryMap H H) : BorelSubset 2 → H →L[ℂ] H :=
  Classical.epsilon (IsUnitarySpectralMeasure U)
end UnitarySpectral
namespace UnitarySpectral
def ExistsUnique : Prop :=
  ∀ (H : Type) [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
    (U : UnitaryMap H H),
    (∃! E : BorelSubset 2 → H →L[ℂ] H, IsUnitarySpectralMeasure U E) ∧
    IsUnitarySpectralMeasure U (unitarySpectralMeasure U) ∧
    ∀ B : H →L[ℂ] H, Commutes B (U.toContinuousLinearEquiv : H →L[ℂ] H) →
      ∀ Δ, Commutes B (unitarySpectralMeasure U Δ)
end UnitarySpectral
end YangMills.Construction.EuclideanBorel
