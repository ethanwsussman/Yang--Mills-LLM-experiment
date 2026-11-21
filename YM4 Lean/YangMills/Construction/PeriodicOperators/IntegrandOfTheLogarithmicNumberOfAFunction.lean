import YangMills.Construction.Matrices.SecondDifferentialOfTheLogarithmOfADeterminant
import YangMills.Construction.PeriodicOperators.RulesOfTheCalculusOfJets
import Mathlib
set_option autoImplicit false
noncomputable section
namespace YangMills.Construction.PeriodicOperators.LogDensityBounds
open Coordinates.ComplexCoordinates.LogDetSecondDeriv (IsHolomorphicScalarIn)
open RiemannSums (HolomorphicNearStrip PeriodicOnStrip)
open JetQuad (IsInvertibleJet logNumber logDensity)
def Claim : Prop :=
  ∀ Q P : PeriodicData, IsPeriodic Q → IsPeriodic P →
    ∀ T : (Q.Carrier → ℂ) → P.Carrier → P.Carrier → ℂ, IsLocalOpFun Q P P T →
    ∀ δ : ℝ, 0 < δ →
      (∀ p ∈ imStrip δ, ∀ εp εm : Q.UnitQuot → ℂ,
        IsInvertibleJet δ p (jetAlong Q P P T p εp εm)) →
      (∃ C : ℝ, 0 < C ∧ ∀ (p : InfiniteLattice.AmbientSpace) (εp εm : Q.UnitQuot → ℂ),
        HolomorphicNearStrip δ
            (logDensity (toComplexVec p) (jetAlong Q P P T (toComplexVec p) εp εm)) ∧
          PeriodicOnStrip δ
            (logDensity (toComplexVec p) (jetAlong Q P P T (toComplexVec p) εp εm)) ∧
          ∀ κ ∈ imStrip δ,
            ‖logDensity (toComplexVec p) (jetAlong Q P P T (toComplexVec p) εp εm) κ‖ ≤
              C * wNorm (Q.quotWeight 1) εp * wNorm (Q.quotWeight 1) εm) ∧
      ∃ O : Set (Fin 4 → ℂ), IsOpen O ∧ imStrip δ ⊆ O ∧
        ∃ a : Q.UnitQuot → Q.UnitQuot → (Fin 4 → ℂ) → ℂ,
          (∀ u u', IsHolomorphicScalarIn O (a u u')) ∧
          ∀ p ∈ imStrip δ, ∀ εp εm : Q.UnitQuot → ℂ,
            logNumber p (jetAlong Q P P T p εp εm) =
              ∑' u, ∑' u', a u u' p * εp u * εm u'
end YangMills.Construction.PeriodicOperators.LogDensityBounds
end
