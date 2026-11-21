import YangMills.Construction.WeightedGreen.DecayRateDefs
import Mathlib
set_option autoImplicit false
noncomputable section
namespace YangMills.Construction.Dirichlet
def FloorsAtRate (d : ℕ) (L δ M R₁ : ℝ) : Prop :=
  M ≥ L + 10 ∧ R₁ * M ≥ max (L * (L + 9)) (((d : ℝ) + 2) * δ⁻¹ * Real.log L)
def BlockGapFloors (d L : ℕ) (aLow aHigh M R₁ : ℝ) : Prop :=
  FloorsAtRate d L (YangMills.Construction.WeightedGreen.expDecayRate d L aLow aHigh) M R₁
end YangMills.Construction.Dirichlet
