import YangMills.Construction.LimitsOfLatticeFamilies.AdmittedRadii
import YangMills.Construction.LimitsOfLatticeFamilies.BoundFunctionsHierarchiesAndLimitData
import Mathlib
set_option autoImplicit false
noncomputable section
namespace YangMills.Construction.LatticeLimits.ModelSpace
variable (s : Conventions.StandingParameters)
def torusFactor (M : ℕ) : ℝ := 16 ^ 4 * (1 + 320 * Real.pi * M)
def refRadius : ModelSpace → ℝ
  | .euclidean => 1
  | .torus => (s.L : ℝ) ^ (s.m : ℕ) / 4
theorem refRadius_torus_eq_side_div_eight : refRadius s .torus = s.side / 8 := by
  simp only [refRadius, Conventions.StandingParameters.side, PeriodicLattice.torusSide]
  ring
def costFactor (M : ℕ) : ModelSpace → ℝ
  | .euclidean => 1
  | .torus => torusFactor M
variable (Y : ModelSpace)
open scoped Classical in
def effConstOf (r Θ : ℝ) (C : SeparationBound) (n : ℕ) (d R : ℝ) : ℝ :=
  if R ∈ admissibleRadii s Y then C.val n d R else Θ ^ n * C.val n d r
open scoped Classical in
def flatRadiusOf (r R : ℝ) : ℝ := if R ∈ admissibleRadii s Y then R else r
open scoped Classical in
def effConst (M : ℕ) (C : SeparationBound) (n : ℕ) (d R : ℝ) : ℝ :=
  if R ∈ admissibleRadii s Y then C.val n d R
  else costFactor M Y ^ n * C.val n d (refRadius s Y)
open scoped Classical in
def flatRadius (R : ℝ) : ℝ := if R ∈ admissibleRadii s Y then R else refRadius s Y
end YangMills.Construction.LatticeLimits.ModelSpace
end
