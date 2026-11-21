import YangMills.Construction.EuclideanBorel.RepresentationSpectralMeasure
import YangMills.Construction.HilbertSpaces.FormsOperatorsAndFamiliesInAHilbertSpace
import Mathlib
set_option autoImplicit false
noncomputable section
namespace YangMills.Construction.EuclideanBorel
open YangMills.Construction.FormsOperators (IsStronglyContUnitaryRep Commutes UnitaryMap)
namespace UnitaryRep
def SpectralCorrespondence : Prop :=
  ∀ (H : Type) [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H] (n : ℕ), 1 ≤ n →
    (∀ E : BorelSubset n → H →L[ℂ] H, IsPVM E →
      ∃ V : Space n → UnitaryMap H H, IsStronglyContUnitaryRep V ∧
        ∀ v, SpectralIntegralIs E (expChar v) (V v)) ∧
    ∀ V : Space n → UnitaryMap H H, IsStronglyContUnitaryRep V →
      (∃! E : BorelSubset n → H →L[ℂ] H, IsSpectralMeasureOf V E) ∧
      IsSpectralMeasureOf V (spectralMeasureOf V) ∧
      ∀ B : H →L[ℂ] H, (∀ v, Commutes B ((V v).toContinuousLinearEquiv : H →L[ℂ] H)) →
        ∀ Δ, Commutes B (spectralMeasureOf V Δ)
end UnitaryRep
end YangMills.Construction.EuclideanBorel
