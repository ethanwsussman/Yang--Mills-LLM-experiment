import YangMills.Construction.Matrices.SecondDifferentialOfTheLogarithmOfADeterminant
import YangMills.Construction.PeriodicOperators.Jets
import Mathlib
set_option autoImplicit false
open Set
noncomputable section
namespace YangMills.Construction.PeriodicOperators.StripBound
open YangMills.Construction.Coordinates.ComplexCoordinates.LogDetSecondDeriv (IsHolomorphicScalarIn)
open JetQuad (IsInvertibleJet IsJet EqAsJet logNumber)
variable (F I : PeriodicData)
def logDetForm (T : (F.Carrier → ℂ) → I.Carrier → I.Carrier → ℂ) (p : Fin 4 → ℂ)
    (u v : F.UnitQuot → ℂ) : ℂ :=
  logNumber p (jetAlong F I I T p u v)
open Classical in
structure IsAdmissibleWidth (T : (F.Carrier → ℂ) → I.Carrier → I.Carrier → ℂ) (δ : ℝ) : Prop where
  invertible : ∀ p ∈ imStrip δ, ∀ u v : F.UnitQuot → ℂ,
    IsInvertibleJet δ p (jetAlong F I I T p u v)
  bilinear : ∀ p ∈ imStrip δ, ∃ B : (F.UnitQuot → ℂ) →ₗ[ℂ] (F.UnitQuot → ℂ) →ₗ[ℂ] ℂ,
    ∀ u v : F.UnitQuot → ℂ, logDetForm F I T p u v = B u v
  coefficients_holomorphic : ∀ c c' : F.UnitQuot, ∃ O : Set (Fin 4 → ℂ), IsOpen O ∧ imStrip δ ⊆ O ∧
    ∃ g : (Fin 4 → ℂ) → ℂ, IsHolomorphicScalarIn O g ∧ ∀ p ∈ imStrip δ,
      g p = logDetForm F I T p (Pi.single c 1) (Pi.single c' 1)
def LogNumberWidthIndependent (T : (F.Carrier → ℂ) → I.Carrier → I.Carrier → ℂ) : Prop :=
  ∀ (p : Fin 4 → ℂ) (u v : F.UnitQuot → ℂ) (δ₁ δ₂ : ℝ) (S₁ S₂ : JetQuad I I),
    0 < δ₁ → p ∈ imStrip δ₁ → IsInvertibleJet δ₁ p (jetAlong F I I T p u v) →
    IsJet δ₁ p S₁ → EqAsJet δ₁ p S₁ (jetAlong F I I T p u v) →
    0 < δ₂ → p ∈ imStrip δ₂ → IsInvertibleJet δ₂ p (jetAlong F I I T p u v) →
    IsJet δ₂ p S₂ → EqAsJet δ₂ p S₂ (jetAlong F I I T p u v) →
      logNumber p S₁ = logNumber p S₂
def LogDetFormQuasiPeriodic (T : (F.Carrier → ℂ) → I.Carrier → I.Carrier → ℂ) (δ : ℝ) : Prop :=
  ∀ p ∈ imStrip δ, ∀ (u v : F.UnitQuot → ℂ) (e : Fin 4 → ℤ),
    addTwoPiInt p e ∈ imStrip δ ∧
      logDetForm F I T (addTwoPiInt p e) u v =
        logDetForm F I T p (phaseMul F e u) (phaseMul F (-e) v)
def IsLogDetFormBound (T : (F.Carrier → ℂ) → I.Carrier → I.Carrier → ℂ) (δ M : ℝ) : Prop :=
  ∀ p ∈ imStrip δ, ∀ u v : F.UnitQuot → ℂ,
    ‖logDetForm F I T p u v‖ ≤
      M * wNorm (F.quotWeight 1) u * wNorm (F.quotWeight 1) v
def unitBallValues (T : (F.Carrier → ℂ) → I.Carrier → I.Carrier → ℂ) (δ : ℝ) : Set ℝ :=
  {r | ∃ p ∈ imStrip δ, ∃ u v : F.UnitQuot → ℂ,
    wNorm (F.quotWeight 1) u ≤ 1 ∧ wNorm (F.quotWeight 1) v ≤ 1 ∧
      r = ‖logDetForm F I T p u v‖}
def unitBallSup (T : (F.Carrier → ℂ) → I.Carrier → I.Carrier → ℂ) (δ : ℝ) : ℝ :=
  sSup (unitBallValues F I T δ)
def Claim : Prop :=
  ∀ F I : PeriodicData, IsPeriodic F → IsPeriodic I →
    ∀ T : (F.Carrier → ℂ) → I.Carrier → I.Carrier → ℂ, IsLocalOpFun F I I T →
      (∀ κ : InfiniteLattice.AmbientSpace,
        IsUnit (symbolHom I I (coeffZero F I I T) (toComplexVec κ) :
          Module.End ℂ (I.UnitQuot → ℂ))) →
      ∀ δ : ℝ, 0 < δ → IsAdmissibleWidth F I T δ →
        LogNumberWidthIndependent F I T ∧
        LogDetFormQuasiPeriodic F I T δ ∧
        (∃ M : ℝ, IsLogDetFormBound F I T δ M) ∧
        BddAbove (unitBallValues F I T δ) ∧
        IsLogDetFormBound F I T δ (unitBallSup F I T δ)
end YangMills.Construction.PeriodicOperators.StripBound
end
