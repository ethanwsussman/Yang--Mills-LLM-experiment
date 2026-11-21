import YangMills.Construction.SummableBoundsOfTheFlow.TransportAtSixDerivatives
import Mathlib
set_option autoImplicit false
noncomputable section
namespace YangMills.Construction
open BlockAverages
namespace ColdStepAtMirrorFrames
open Interpolation (rateParameters)
open Classical in
def decayThresholdIndex (U : StepParameters) : ℕ :=
  if h : ∃ ns : ℕ, ∀ n : ℕ, ns ≤ n → 2 ^ 10 * ((U.L : ℝ) ^ 4 * U.Ct) * torusDecayFactor U.L U.decayRate n *
      (1 / torusDecayFactor U.L U.decayRate ((U.L : ℝ) * n / 16) + Real.exp (-(2 ^ 6 * U.κ * n))) ≤ 1
  then h.choose else 0
def TransportConditionsAt (T : StepParameters) (q : ℝ) : Prop :=
  T.IsOrdered ∧ 2 ^ 40 ≤ T.L ∧ 0 < T.Ct ∧ 8 * T.blockIndex + 8 ≤ T.n₀ ∧
    decayThresholdIndex (rateParameters T) ≤ T.blockIndex ∧
    (∀ n : ℕ, decayThresholdIndex (rateParameters T) ≤ n →
      2 ^ 10 * ((T.L : ℝ) ^ 4 * T.Ct) * torusDecayFactor T.L T.decayRate n *
      (1 / torusDecayFactor T.L T.decayRate ((T.L : ℝ) * n / 16) + Real.exp (-(2 ^ 6 * T.κ * n))) ≤ 1) ∧
    q * T.η₃ ≤ 2⁻¹ ^ 9
def transportConditionsEventually : Prop :=
  ∀ Q : StepParameters → ℝ, EventuallyInParameters fun T => TransportConditionsAt T (Q (rateParameters T))
end ColdStepAtMirrorFrames
end YangMills.Construction
end
