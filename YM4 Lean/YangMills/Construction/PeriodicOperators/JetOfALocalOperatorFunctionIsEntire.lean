import YangMills.Construction.PeriodicOperators.ExponentialSumsTorusWavesAndComponentSets
import Mathlib
set_option autoImplicit false
open Set
open scoped ENNReal
noncomputable section
namespace YangMills.Construction.PeriodicOperators.LocalJetEntire
open JetDomains
open JetQuad (IsJet EqAsJet)
def Claim : Prop :=
  ∀ F I I' : PeriodicData, IsPeriodic F → IsPeriodic I → IsPeriodic I' →
    ∀ T : (F.Carrier → ℂ) → I'.Carrier → I.Carrier → ℂ, IsLocalOpFun F I I' T →
      (∀ (εPlus εMinus : F.UnitQuot → ℂ) (c' : I'.UnitQuot) (c : I.UnitQuot),
        Coordinates.ComplexCoordinates.IsHolomorphicIn (N := 4 + 4) (N' := 1) univ fun z _ =>
          linearMapEntry ((jetAlong F I I' T (sndMomentum z) εPlus εMinus).f10 (fstMomentum z)) c' c) ∧
      (∀ (εPlus εMinus : F.UnitQuot → ℂ) (c' : I'.UnitQuot) (c : I.UnitQuot),
        Coordinates.ComplexCoordinates.IsHolomorphicIn (N := 4 + 4) (N' := 1) univ fun z _ =>
          linearMapEntry ((jetAlong F I I' T (sndMomentum z) εPlus εMinus).f01 (fstMomentum z)) c' c) ∧
      (∀ (εPlus εMinus : F.UnitQuot → ℂ) (c' : I'.UnitQuot) (c : I.UnitQuot),
        Coordinates.ComplexCoordinates.IsHolomorphicIn (N := 4 + 4) (N' := 1) univ fun z _ =>
          linearMapEntry ((jetAlong F I I' T (sndMomentum z) εPlus εMinus).f11 (fstMomentum z)) c' c) ∧
      ∀ (δ : ℝ), 0 < δ → ∀ p ∈ imStrip δ, ∀ εPlus εMinus : F.UnitQuot → ℂ,
        IsJet δ p (jetAlong F I I' T p εPlus εMinus)
end YangMills.Construction.PeriodicOperators.LocalJetEntire
end
