import YangMills.Construction.SummableBoundsOfTheFlow.ExpansionsOfTheLevels
import YangMills.Construction.SummableBoundsOfTheFlow.MixtureAtTheFlatField
import Mathlib
set_option autoImplicit false
noncomputable section
open scoped Topology
namespace YangMills.Construction.CriticalGerms
def interpInverseDecayStatement : Prop :=
  ColdStepAtMirrorFrames.EventuallyOrdered fun T => ∀ [NeZero T.L], ∀ r : ℝ, 0 ≤ r →
    TwoLevelMixtures.LevelExpansionsBounded T r →
    ∀ (t n : ℕ) [NeZero n] (θ : ℝ) (b₀ : TorusFields.TorusBond (n * T.L)) (g : TorusFields.TorusBond (n * T.L) → ℝ),
      64 ≤ n → 0 ≤ θ → θ ≤ 1 →
      b₀ ∈ StepCosts.chartBonds T.L n →
      TwoLevelMixtures.SolvesShiftedEq T.a T.L t θ 1 T.lam (MixtureJets.bondIndicator b₀) g →
      ∀ b : TorusFields.TorusBond (n * T.L),
        |g b| ≤ 2 / T.lam * Real.exp (-(2 * r *
          TorusFields.supDist (TorusLumps.parentBlock T.L b.1) (TorusLumps.parentBlock T.L b₀.1)))
end YangMills.Construction.CriticalGerms
end
