import YangMills.Construction.ColdChainAtEveryLevel.DecayOnATorusForm
import Mathlib
set_option autoImplicit false
noncomputable section
namespace YangMills.Construction.LinearResponse
open BlockAverages
def DecayFactorExpBound : Prop :=
  ∀ (L : ℕ) (δ : ℝ), 0 < L → 0 < δ → ∃ C : ℝ, 1 ≤ C ∧ ∀ u : ℝ, 0 ≤ u →
    torusDecayFactor L δ u ≤ C * Real.exp (2 * δ * u)
end YangMills.Construction.LinearResponse
end
