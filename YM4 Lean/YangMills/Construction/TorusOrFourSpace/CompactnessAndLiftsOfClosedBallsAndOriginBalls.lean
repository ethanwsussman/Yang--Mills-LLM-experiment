import YangMills.Construction.Lattice.ObservablesAndTestNorms
import YangMills.Construction.TorusOrFourSpace.OriginClosedBallsAndBallsAboutTheOrigin
import Mathlib
set_option autoImplicit false
open scoped ENNReal
noncomputable section
namespace YangMills.Construction.PeriodicSpace
open Kind
def BallCompactnessAndTorusLifts : Prop :=
  ∀ D : Params,
    (∀ (E : Kind) (x : E.Pt D) (R : ℝ), 0 < R → IsCompactQ D E (closedBallAbout D E x R)) ∧
    (∀ x : Pt D torus,
      (∀ R : ℝ, 0 < R → R < D.side / 2 →
        closedBallAbout D torus x R = TestFunctions.closedBallTorus (ℓ := D.side) x R) ∧
      (∀ R : ℝ, D.side ≤ R → closedBallAbout D torus x R = Set.univ)) ∧
    (∀ ρ : ℝ≥0∞, 0 < ρ → ρ < ∞ →
      centredBall D torus ρ =
        quotMap D torus '' {x | TorusMetric.euclidNormVec x < ρ.toReal}) ∧
    (∀ y : Pt D torus, ∃ x : Fin 4 → ℝ, IsLift D torus y x ∧
      ∀ μ, x μ ∈ Set.Icc (-(D.side / 2)) (D.side / 2)) ∧
    (∀ v : Fin 4 → ℝ, (∀ μ, v μ ∈ Set.Icc (-(D.side / 2)) (D.side / 2)) →
      TorusMetric.euclidNormVec v ≤ D.side) ∧
    (∀ ρ : ℝ≥0∞, ENNReal.ofReal D.side < ρ → centredBall D torus ρ = Set.univ) ∧
    (∀ (E : Kind) (S : Set (E.Pt D)), IsCompactQ D E S →
      ∃ ρ : ℝ≥0∞, 0 < ρ ∧ ρ < ∞ ∧ S ⊆ centredBall D E ρ) ∧
    (∀ (x : Pt D torus) (R : ℝ) (xl : Fin 4 → ℝ), 0 < R → R < D.side / 4 →
      IsLift D torus x xl →
        setDiam D torus (closedBallAbout D torus x R) ≤ ENNReal.ofReal (2 * R) ∧
        2 * R < D.side / 2 ∧
        quotMap D torus '' TestFunctions.closedBallR4 xl R = closedBallAbout D torus x R ∧
        ∀ z ∈ TestFunctions.closedBallR4 xl R, ∀ z' ∈ TestFunctions.closedBallR4 xl R,
          quotDist D torus (quotMap D torus z) (quotMap D torus z') =
            TorusMetric.euclidNormVec (z - z'))
end YangMills.Construction.PeriodicSpace
