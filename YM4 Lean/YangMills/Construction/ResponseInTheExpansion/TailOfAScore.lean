import YangMills.Construction.ResponseInTheExpansion.LawOfTheColdHalf
import YangMills.Construction.SummableBoundsOfTheFlow.ScaledVariablesOfTheStep
import Mathlib
set_option autoImplicit false
noncomputable section
namespace YangMills.Construction
open BlockAverages ColdStepAtMirrorFrames ScaledVariables
namespace WeightedResponses
variable {F : BlockFrame}
namespace ColdHalfLaw
variable (Q : ColdHalfLaw)
def scoreRemainder (r : ℝ) : ℝ :=
  - deriv haarGapTail (1 / (Q.a * Q.coupling * r)) / (Q.a ^ 2 * r)
def scoreRemainderAt (c : F.Site F.top × Fin 4) : AboveFrames F :=
  fun η V => Q.scoreRemainder (Q.contourAverageSize c η V)
def scoreRemainderIncrement (c : F.Site F.top × Fin 4) : AboveFrames F :=
  fun η V => Q.scoreRemainderAt c η V - Q.scoreRemainderAt c 0 V
end ColdHalfLaw
def ScoreRemainderExpansion : Prop :=
  (∀ (Q : ColdHalfLaw) (r : ℝ), 1 ≤ Q.a * Q.coupling * r → 0 < r →
    r * deriv haarGap (Q.a * Q.coupling * r) =
      3 / (2 * Q.a * Q.coupling) + (Q.coupling ^ 2)⁻¹ * Q.scoreRemainder r) ∧
  ∀ a : ℝ, 1 ≤ a → ∀ k : ℕ, ∃ C : ℝ, ∀ Q : ColdHalfLaw, Q.a = a → 2 / a ≤ Q.coupling →
    ContDiffOn ℝ (k : ℕ∞) Q.scoreRemainder (Set.Icc (1 / 2) 1) ∧
    ∀ r ∈ Set.Icc (1 / 2 : ℝ) 1,
      |iteratedDerivWithin k Q.scoreRemainder (Set.Icc (1 / 2) 1) r| ≤ C
end WeightedResponses
end YangMills.Construction
end
