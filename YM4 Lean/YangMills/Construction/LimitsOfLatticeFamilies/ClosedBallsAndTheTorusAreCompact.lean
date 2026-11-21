import YangMills.Construction.LimitsOfLatticeFamilies.SpaceLengthAndBallsAtEveryRadius
import Mathlib
set_option autoImplicit false
open Set
open scoped ENNReal
noncomputable section
namespace YangMills.Construction.LatticeLimits
open ModelSpace
namespace CompactBallsAndTorus
def Claim : Prop :=
  ∀ s : Conventions.StandingParameters,
    (∀ Y : ModelSpace,
      (∀ (x : Y.Carrier s) (R : ℝ), 0 < R → IsCompactIn s Y (ModelSpace.closedBall s Y x R)) ∧
      ∀ S : Set (Y.Carrier s), IsCompactIn s Y S →
        (∃ ρ : ℝ, 0 < ρ ∧ S ⊆ ballAtBase s Y (ENNReal.ofReal ρ)) ∧
        ∃ (x : Y.Carrier s) (R : ℝ), 0 < R ∧ S ⊆ ModelSpace.closedBall s Y x R) ∧
    (∀ z : ModelSpace.torus.Carrier s, ∃ v : Fin 4 → ℝ, IsLiftOf s ModelSpace.torus z v ∧
      ∀ μ, v μ ∈ Icc (-(s.side / 2)) (s.side / 2)) ∧
    (∀ z : ModelSpace.torus.Carrier s, ModelSpace.norm s ModelSpace.torus z ≤ s.side) ∧
    IsCompactIn s ModelSpace.torus univ ∧
    ∀ (x : ModelSpace.torus.Carrier s) (R : ℝ), s.side ≤ R →
      ModelSpace.closedBall s ModelSpace.torus x R = univ
end CompactBallsAndTorus
end YangMills.Construction.LatticeLimits
end
