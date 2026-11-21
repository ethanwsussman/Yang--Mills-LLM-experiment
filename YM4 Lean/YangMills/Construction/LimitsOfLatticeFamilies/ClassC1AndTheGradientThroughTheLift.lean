import YangMills.Construction.LimitsOfLatticeFamilies.SpaceLengthAndBallsAtEveryRadius
import Mathlib
set_option autoImplicit false
noncomputable section
namespace YangMills.Construction.LatticeLimits
open ModelSpace
namespace C1ViaLift
def Claim : Prop :=
  ∀ (s : Conventions.StandingParameters) (Y : ModelSpace),
    (∀ f : Y.Carrier s → ℝ, IsC1 s Y f ↔ TestFunctions.IsC1R4 (f ∘ proj s Y)) ∧
    (∀ f : Y.Carrier s → ℝ, IsC1 s Y f →
      grad s Y f ∘ proj s Y = gradR4 (f ∘ proj s Y) ∧
      ∀ g : Y.Carrier s → Fin 4 → ℝ,
        g ∘ proj s Y = gradR4 (f ∘ proj s Y) → g = grad s Y f) ∧
    ∀ f g : Y.Carrier s → ℝ, IsC1 s Y f → IsC1 s Y g →
      (∀ a b : ℝ, IsC1 s Y (a • f + b • g)) ∧ IsC1 s Y (f * g)
end C1ViaLift
end YangMills.Construction.LatticeLimits
end
