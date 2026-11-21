import YangMills.Construction.LimitsOfLatticeFamilies.SpaceLengthAndBallsAtEveryRadius
import Mathlib
set_option autoImplicit false
open Set
noncomputable section
namespace YangMills.Construction.LatticeLimits.ModelSpace
variable (s : Conventions.StandingParameters)
def maxRadius : ℝ := (s.L : ℝ) ^ (s.m : ℕ) / 2
theorem maxRadius_eq_side_div_four : maxRadius s = s.side / 4 := by
  simp only [maxRadius, Conventions.StandingParameters.side, PeriodicLattice.torusSide]
  ring
def admissibleRadii : ModelSpace → Set ℝ
  | .euclidean => Ioi 0
  | .torus => Ioo 0 (maxRadius s)
end YangMills.Construction.LatticeLimits.ModelSpace
end
