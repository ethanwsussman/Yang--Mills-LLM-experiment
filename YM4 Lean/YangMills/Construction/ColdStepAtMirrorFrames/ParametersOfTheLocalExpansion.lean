import YangMills.Construction.ColdStepAtMirrorFrames.ParametersOfTheColdStep
import Mathlib
set_option autoImplicit false
noncomputable section
namespace YangMills.Construction
open BlockAverages
namespace ColdStepAtMirrorFrames
def localExpansionTail (T : StepParameters) (A : ℝ) (r : ℕ) : ℝ :=
  (T.L : ℝ) ^ 4 * A * (1 / torusDecayFactor T.L T.decayRate ((T.L * (r / 4) : ℕ) : ℝ) +
    (1 / T.η₃) * (2 * ((T.L * (r / 4) : ℕ) : ℝ) + 5) ^ 4 * Real.exp (-(T.chainParams.δ₂ / 8 * r)))
def LocalExpansionParametersAt (A : ℝ → ℕ → ColdChainParameters → ℝ → ℝ) (T : StepParameters) : Prop :=
  ∀ r : ℕ, T.blockIndex ≤ r → 16 ≤ r ∧ T.Ct * Real.exp (-(T.chainParams.δ₂ / 8 * r)) ≤ 1 / 64 ∧
    localExpansionTail T (A T.a T.L T.chainParams T.Ct) r ≤ 2⁻¹ ^ 8 / torusDecayFactor T.L T.decayRate r
def LocalExpansionParametersEventually : Prop :=
  ∀ A : ℝ → ℕ → ColdChainParameters → ℝ → ℝ, EventuallyInParameters (LocalExpansionParametersAt A)
end ColdStepAtMirrorFrames
end YangMills.Construction
end
