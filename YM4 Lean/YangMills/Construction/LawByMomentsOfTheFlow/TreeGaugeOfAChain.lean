import YangMills.Construction.LawByMomentsOfTheFlow.GaussianChainOfTheLaw
import Mathlib
set_option autoImplicit false
noncomputable section
namespace YangMills.Construction.MomentLaw
def treeGaugeFixingStatement : Prop :=
  ∀ (L : ℕ) [NeZero L], Odd L → ∀ (s n : ℕ) [NeZero n], 64 ≤ n →
    ∃ G : LevelChain L s n →ₗ[ℝ] LevelChain L s n,
      ∀ X, IsTreeGauge s n (G X) ∧ ∀ a : ℝ, levelEnergy a s n (G X - X) = 0
end YangMills.Construction.MomentLaw
end
