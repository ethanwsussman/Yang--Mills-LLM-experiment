import YangMills.Construction.Parameters.OrderOfChoice
import Mathlib
set_option autoImplicit false
noncomputable section
namespace YangMills.Construction.ParameterChoice
def cutoffLogExponent (c : ChoiceUpToCoupling) (x : ℝ) : ℝ :=
  1 / 20 * secondCouplingScale c.cHat c.L c.M * c.A₁ ^ 2 * Real.log x ^ (2 * c.𝔭₀)
def flowConstantCutoffBound (T : DerivedConstants) (c : ChoiceUpToCoupling) :
    TailCeiling where
  fn x := T.C₁Fl c.toChoiceUpToDegreeConstants * c.A₁ * x ^ (-(1 / 2) : ℝ) * Real.log x ^ c.𝔭₀
  bound := c.εI₁
def cubeSizeCutoffBound (c : ChoiceUpToCoupling) : TailCeiling where
  fn x := 4 * (c.M : ℝ) ^ 4 * Real.exp (-(2 * cutoffLogExponent c x)) / cutoffLogExponent c x
  bound := 1
def decayRateCutoffBound (c : ChoiceUpToCoupling) : TailCeiling where
  fn x := 1 / cutoffLogExponent c x
  bound := 1 / (4 * c.κ)
def widthCutoffBound (c : ChoiceUpToCoupling) : TailCeiling where
  fn x := 32 * Real.exp (-cutoffLogExponent c x)
  bound := windowWidth c.rStar c.L * c.κ
def cutoffBounds (T : DerivedConstants) : List (ChoiceUpToCoupling → TailCeiling) :=
  [flowConstantCutoffBound T, cubeSizeCutoffBound, decayRateCutoffBound, widthCutoffBound]
def CutoffBoundsIncluded (T : DerivedConstants) (N : ExternalConstants) : Prop :=
  ∀ p ∈ cutoffBounds T, p ∈ N.cutoffCeilings
end YangMills.Construction.ParameterChoice
end
