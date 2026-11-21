import YangMills.Construction.PeriodicOperators.EntriesAtTheClassesAndMapsIntoHom
import YangMills.Construction.PeriodicOperators.SecondDifferentialsAreBoundedOnAStrip
import YangMills.Construction.PeriodicOperators.SecondDifferentialsOfLogarithmsOfDeterminants
import YangMills.Construction.Towers.TheJetsOfTheTwoOperatorFunctions
import Mathlib
set_option autoImplicit false
open Set
noncomputable section
namespace YangMills.Construction.PeriodicOperators.InvertibleJetWidths
open YangMills.Construction.Coordinates.ComplexCoordinates.LogDetSecondDeriv (IsHolomorphicScalarIn)
open YangMills.Construction.PeriodicOperators.LogDetSecondDerivs
  (normalizedDet ofCoords logDetInCoords logDetSecondDeriv IsCloseToLogNumber)
open YangMills.Construction.PeriodicOperators.StripBound (IsAdmissibleWidth logDetForm)
open YangMills.Construction.PeriodicOperators.JetQuad (IsInvertibleJet IsJet EqAsJet logNumber)
variable (F I : PeriodicData)
def JetsInvertibleDichotomy (T : (F.Carrier → ℂ) → I.Carrier → I.Carrier → ℂ) (δ : ℝ) : Prop :=
  (∀ p ∈ imStrip δ, ∀ εp εm : F.UnitQuot → ℂ,
      IsInvertibleJet δ p (jetAlong F I I T p εp εm)) ∨
    ∀ p ∈ imStrip δ, ∀ εp εm : F.UnitQuot → ℂ,
      ¬ IsInvertibleJet δ p (jetAlong F I I T p εp εm)
def SymbolInvertibleBoundedInverse (T : (F.Carrier → ℂ) → I.Carrier → I.Carrier → ℂ) (δ : ℝ) :
    Prop :=
  (∀ κ ∈ imStrip (2 * δ),
    IsUnit (symbolHom I I (coeffZero F I I T) κ : Module.End ℂ (I.UnitQuot → ℂ))) ∧
  QuotHomFamilyBoundedOn (imStrip (2 * δ)) fun κ =>
    quotHomInverse (symbolHom I I (coeffZero F I I T) κ)
def LogNumberIndependentOfWidth (T : (F.Carrier → ℂ) → I.Carrier → I.Carrier → ℂ)
    (p : Fin 4 → ℂ) (εp εm : F.UnitQuot → ℂ) : Prop :=
  ∀ (δ₁ δ₂ : ℝ) (S₁ S₂ : JetQuad I I),
    HasInvertibleJetsAtWidth F I T δ₁ → p ∈ imStrip δ₁ →
    IsJet δ₁ p S₁ → EqAsJet δ₁ p S₁ (jetAlong F I I T p εp εm) →
    HasInvertibleJetsAtWidth F I T δ₂ → p ∈ imStrip δ₂ →
    IsJet δ₂ p S₂ → EqAsJet δ₂ p S₂ (jetAlong F I I T p εp εm) →
      logNumber p S₁ = logNumber p S₂
open Classical in
def CoeffsHolomorphicOnInterior (T : (F.Carrier → ℂ) → I.Carrier → I.Carrier → ℂ) (δ : ℝ) :
    Prop :=
  imStrip δ ⊆ interior (imStrip (2 * δ)) ∧
  ∀ c c' : F.UnitQuot, ∃ g : (Fin 4 → ℂ) → ℂ,
    IsHolomorphicScalarIn (interior (imStrip (2 * δ))) g ∧
      ∀ p ∈ imStrip δ, g p = logDetForm F I T p (Pi.single c 1) (Pi.single c' 1)
def SecondDerivsEventuallyClose (T : (F.Carrier → ℂ) → I.Carrier → I.Carrier → ℂ) : Prop :=
  ∃ (s₁ : ℕ) (C c : ℝ), 0 < s₁ ∧ 0 < C ∧ 0 < c ∧ ∀ s : ℕ, s₁ ≤ s →
    IsUnit (LogDetSecondDerivs.quotOperator F I T s 0) ∧
    ∀ (N : ℕ) (e : Fin N ≃ F.QuotMod s),
      (∃ W : Set (Coordinates.ComplexCoordinates N), IsOpen W ∧ 0 ∈ W ∧
        (∀ z ∈ W, ‖normalizedDet F I T s (ofCoords e z) - 1‖ < 1) ∧
        IsHolomorphicScalarIn W (logDetInCoords F I T e)) ∧
      IsCloseToLogNumber F I T s (logDetSecondDeriv F I T e) C c
def Claim : Prop :=
  ∀ F I : PeriodicData, IsPeriodic F → IsPeriodic I →
    ∀ T : (F.Carrier → ℂ) → I.Carrier → I.Carrier → ℂ, IsLocalOpFun F I I T →
      (∀ δ : ℝ, 0 < δ →
        JetsInvertibleDichotomy F I T δ ∧
        ((∀ p ∈ imStrip δ, ∀ εp εm : F.UnitQuot → ℂ,
            IsInvertibleJet δ p (jetAlong F I I T p εp εm)) ↔
          SymbolInvertibleBoundedInverse F I T δ)) ∧
      ∀ δ : ℝ, HasInvertibleJetsAtWidth F I T δ →
        ((∀ δ' : ℝ, 0 < δ' → δ' ≤ δ → HasInvertibleJetsAtWidth F I T δ') ∧
          ∃ η : ℝ, δ < η ∧ HasInvertibleJetsAtWidth F I T η) ∧
        (∀ p ∈ imStrip δ, ∀ εp εm : F.UnitQuot → ℂ,
          LogNumberIndependentOfWidth F I T p εp εm) ∧
        (∀ κ : InfiniteLattice.AmbientSpace,
          IsUnit (symbolHom I I (coeffZero F I I T) (toComplexVec κ) :
            Module.End ℂ (I.UnitQuot → ℂ))) ∧
        IsAdmissibleWidth F I T δ ∧
        CoeffsHolomorphicOnInterior F I T δ ∧
        SecondDerivsEventuallyClose F I T
end YangMills.Construction.PeriodicOperators.InvertibleJetWidths
end
