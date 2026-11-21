import YangMills.Construction.TorusOrFourSpace.OriginClosedBallsAndBallsAboutTheOrigin
import Mathlib
set_option autoImplicit false
open scoped ENNReal
noncomputable section
namespace YangMills.Construction.PeriodicSpace
open Kind
def ClosedBallsCompactAndCover : Prop :=
  ∀ D : Params,
    (∀ (E : Kind) (x : E.Pt D) (R : ℝ), 0 < R → IsCompactQ D E (closedBallAbout D E x R)) ∧
    ((∀ y : Pt D torus, ∃ x : Fin 4 → ℝ, IsLift D torus y x ∧
        ∀ μ, x μ ∈ Set.Icc (-(D.side / 2)) (D.side / 2)) ∧
      (∀ ρ : ℝ≥0∞, ENNReal.ofReal D.side < ρ → ρ < ∞ → centredBall D torus ρ = Set.univ)) ∧
    (∀ (E : Kind) (S : Set (E.Pt D)), IsCompactQ D E S →
      ∃ ρ : ℝ≥0∞, 0 < ρ ∧ ρ < ∞ ∧ S ⊆ centredBall D E ρ) ∧
    (∀ (E : Kind) (S : Set (E.Pt D)) (R : ℝ), IsCompactQ D E S → 0 < R →
      setDiam D E S ≤ ENNReal.ofReal R →
        ∃ B : Set (E.Pt D), IsClosedBallWithRadius D E B R ∧ S ⊆ B)
end YangMills.Construction.PeriodicSpace
