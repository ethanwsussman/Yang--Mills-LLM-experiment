import YangMills.Construction.OneLoopLaw.OneLoopLawForTheNormalisers
import YangMills.Construction.RunningCouplingSlope.LogarithmOfTheChain
import Mathlib
set_option autoImplicit false
noncomputable section
namespace YangMills.Construction.RunningCouplingSlope
def ChainNearNormaliserSum : Prop :=
  ∀ a : ℝ, 0 < a → ∀ (L : ℕ) (hL : 0 < L), Conventions.IsAdmissibleBlockingFactor L →
    ∃ C : ℝ, 0 ≤ C ∧
    ∀ (k : ℕ) (ρ v : ℝ), 0 < ρ → ρ ≤ 1 →
      SlopeCoefficient.HasSlopeCoefficient Filter.atTop (SlopeCoefficient.chainLogarithm a ρ L k) v →
      |v - ∑ j ∈ Finset.range k, OneLoopLaw.NormaliserLaw.normaliserStiffness hL j| ≤ C
end YangMills.Construction.RunningCouplingSlope
end
