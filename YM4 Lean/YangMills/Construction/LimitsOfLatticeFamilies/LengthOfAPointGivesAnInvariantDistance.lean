import YangMills.Construction.LimitsOfLatticeFamilies.SpaceLengthAndBallsAtEveryRadius
import Mathlib
set_option autoImplicit false
noncomputable section
namespace YangMills.Construction.LatticeLimits
open ModelSpace
def InvariantDistFromNorm.Claim : Prop :=
  ∀ (s : Conventions.StandingParameters) (Y : ModelSpace),
    (∀ z z' : Y.Carrier s, ModelSpace.norm s Y (z + z') ≤ ModelSpace.norm s Y z + ModelSpace.norm s Y z') ∧
    (∀ z : Y.Carrier s, ModelSpace.norm s Y (-z) = ModelSpace.norm s Y z) ∧
    (∀ x y : Y.Carrier s, 0 ≤ ModelSpace.dist s Y x y) ∧
    (∀ x y : Y.Carrier s, ModelSpace.dist s Y x y = 0 ↔ x = y) ∧
    (∀ x y : Y.Carrier s, ModelSpace.dist s Y x y = ModelSpace.dist s Y y x) ∧
    (∀ x y w : Y.Carrier s, ModelSpace.dist s Y x y ≤ ModelSpace.dist s Y x w + ModelSpace.dist s Y w y) ∧
    ∀ x y a : Y.Carrier s, ModelSpace.dist s Y (x + a) (y + a) = ModelSpace.dist s Y x y
end YangMills.Construction.LatticeLimits
end
