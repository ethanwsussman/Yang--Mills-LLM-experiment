import YangMills.Construction.LimitsOfLatticeFamilies.SpaceLengthAndBallsAtEveryRadius
import Mathlib
set_option autoImplicit false
open Set
noncomputable section
namespace YangMills.Construction.LatticeLimits.ProjKernelAndMinimalLifts
open ModelSpace
def Claim : Prop :=
  ∀ s : Conventions.StandingParameters,
    ({x | proj s ModelSpace.euclidean x = 0} = {0} ∧
      {x | proj s ModelSpace.torus x = 0} = {x | ∃ k : Fin 4 → ℤ, x = fun μ => s.side * k μ}) ∧
    ∀ Y : ModelSpace,
      (∀ x x', proj s Y (x + x') = proj s Y x + proj s Y x') ∧
      Function.Surjective (proj s Y) ∧
      (∀ z : Y.Carrier s, ∃ v, IsMinimalLiftOf s Y z v) ∧
      (∀ x, ModelSpace.norm s Y (proj s Y x) ≤ TorusMetric.euclidNormVec x) ∧
      (∀ x x', ModelSpace.norm s Y (proj s Y x - proj s Y x') ≤
        TorusMetric.euclidNormVec (x - x')) ∧
      ∀ x, (Y = ModelSpace.euclidean ∨ Y = ModelSpace.torus ∧ TorusMetric.euclidNormVec x < s.side / 2) →
        ModelSpace.norm s Y (proj s Y x) = TorusMetric.euclidNormVec x
end YangMills.Construction.LatticeLimits.ProjKernelAndMinimalLifts
end
