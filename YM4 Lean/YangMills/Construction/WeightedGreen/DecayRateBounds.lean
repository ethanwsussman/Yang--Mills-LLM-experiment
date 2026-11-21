import YangMills.Construction.Dirichlet.Parameters
import YangMills.Construction.WeightedGreen.DecayRateDefs
import Mathlib
set_option autoImplicit false
noncomputable section
namespace YangMills.Construction.WeightedGreen.DecayRateSize
def bounds : Prop :=
  ∀ (d L : ℕ) (aLo aHi : ℝ), Dirichlet.Parameters d L aLo aHi →
    0 < WeightedGreen.coercivityConst aLo ∧ WeightedGreen.coercivityConst aLo ≤ 4 ∧
    2 * (d : ℝ) * WeightedGreen.expDecayRate d L aLo aHi * ((L : ℝ) ^ 2 + aHi) =
      1 / 4 * WeightedGreen.coercivityConst aLo ∧
    WeightedGreen.expDecayRate d L aLo aHi ≤ 1 / (2 * (d : ℝ) * (L : ℝ) ^ 2) ∧
    1 / (2 * (d : ℝ) * (L : ℝ) ^ 2) ≤ 1 / (18 * (d : ℝ)) ∧
    Real.exp 1 * WeightedGreen.expDecayRate d L aLo aHi * (L : ℝ) * Real.sqrt (d : ℝ) ≤ 1 ∧
    WeightedGreen.expDecayRate d L aLo aHi * (1 / 2 * (d : ℝ) + 1) ≤ 1 ∧
    WeightedGreen.expDecayRate d L aLo aHi * (d : ℝ) * (L : ℝ) * ((L : ℝ) + 9) ≤ 2
end YangMills.Construction.WeightedGreen.DecayRateSize
