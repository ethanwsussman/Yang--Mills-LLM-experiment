import YangMills.Construction.Towers.FunctionalInTheBackgroundGaugeInTheExponentialChart
import YangMills.Construction.Towers.TheFieldsAndTheTwoOperatorFunctions
import Mathlib
set_option autoImplicit false
noncomputable section
namespace YangMills.Construction.Tower
structure HessianAndComplexExtension (L n k : ℕ)
    [Fintype (PositiveEdge L n k 0)] [Fintype (PositiveEdge L n k k)] : Prop where
  eq_expChartSecondDeriv : ∀ r r' : RealPeriodicField L n k,
    fieldFunctionalSecondDeriv L n k r r' = expChartSecondDeriv r r'
  exists_symm_bilinForm : ∃ B : LinearMap.BilinForm ℝ (RealPeriodicField L n k),
    (∀ r r', B r r' = fieldFunctionalSecondDeriv L n k r r') ∧ ∀ r r', B r r' = B r' r
  isComplexSecondDeriv : IsComplexSecondDeriv L n k (complexSecondDeriv L n k)
  complexSecondDeriv_symm : ∀ ζ ζ' : PeriodicField L n k,
    complexSecondDeriv L n k ζ ζ' = complexSecondDeriv L n k ζ' ζ
def HessianAndComplexExtensionHolds : Prop :=
  ∀ L n k : ℕ, Conventions.IsAdmissibleBlockingFactor L → 0 < n → 1 ≤ k →
    ∀ [Fintype (PositiveEdge L n k 0)] [Fintype (PositiveEdge L n k k)],
      HessianAndComplexExtension L n k
end YangMills.Construction.Tower
end
