import YangMills.Construction.TorusOrFourSpace.NeighbourhoodsInTheDiagonalExtraction
import YangMills.Construction.TorusOrFourSpace.OriginClosedBallsAndBallsAboutTheOrigin
import Mathlib
set_option autoImplicit false
open scoped ENNReal
noncomputable section
namespace YangMills.Construction.PeriodicSpace.DiagonalLimits
def CompactNhdProperties : Prop :=
  ∀ (D : Params) (E : Kind) (S S' : Set (E.Pt D)) (hS : Kind.IsCompactQ D E S)
    (hS' : Kind.IsCompactQ D E S') (η η' : ℝ) (hη : 0 < η) (hη' : 0 < η'),
    (Kind.IsOpenQ D E (openNhdWidth D E S hS η hη) ∧
      Kind.IsCompactQ D E (closedNhdWidth D E S hS η hη) ∧
      S ⊆ openNhdWidth D E S hS η hη ∧
      openNhdWidth D E S hS η hη ⊆ closedNhdWidth D E S hS η hη ∧
      ∃ h₀ : Kind.IsCompactQ D E ∅,
        openNhdWidth D E ∅ h₀ η hη = ∅ ∧
        closedNhdWidth D E ∅ h₀ η hη = ∅) ∧
    (Kind.setInfDist D E S S' - ENNReal.ofReal η - ENNReal.ofReal η' ≤
        Kind.setInfDist D E (closedNhdWidth D E S hS η hη)
          (closedNhdWidth D E S' hS' η' hη') ∧
      (S = ∅ ∨ S' = ∅ →
        Kind.setInfDist D E S S' = ∞ ∧
        Kind.setInfDist D E (closedNhdWidth D E S hS η hη)
          (closedNhdWidth D E S' hS' η' hη') = ∞)) ∧
    (∀ ρ : ℝ, 0 < ρ → S ⊆ Kind.centredBall D E (ENNReal.ofReal ρ) →
      closedNhdWidth D E S hS η hη ⊆
        Kind.closedBallAbout D E (Kind.origin D E) (ρ + η))
end YangMills.Construction.PeriodicSpace.DiagonalLimits
