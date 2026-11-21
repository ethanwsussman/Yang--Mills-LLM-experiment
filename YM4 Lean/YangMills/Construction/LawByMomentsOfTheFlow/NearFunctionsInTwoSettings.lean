import YangMills.Construction.LawByMomentsOfTheFlow.NearlyLocalFunctionsOfTheCases
import YangMills.Construction.LawInAState.LocalFunctionsOfAStep
import Mathlib
set_option autoImplicit false
noncomputable section
open MeasureTheory
namespace YangMills.Construction.MomentLaw
def nearFunctionsTwoSettingsStatement : Prop :=
  WeightedResponses.HoldsAtEveryStep fun _ R _ => ∀ (n : ℕ) [NeZero n]
      (Q Q' : ResponseInTheExpansion.StateFunction R (n * R.params.side))
      (z : TorusFields.TorusSite (n * R.params.side)) (K ρ : ℝ),
      R.params.n₀ ≤ n → 0 ≤ ρ → IsNearlyLocalStateFunction R Q z K ρ → IsNearlyLocalStateFunction R Q' z K ρ →
      ∀ (s s' : StepSettings.ChartSetting R n) (m : ℕ), s.IsAdmissible → s'.IsAdmissible →
        ρ / 4 + (R.range : ℝ) / (4 * R.params.side) ≤ m →
        StepSettings.SettingsAgreeNear s s' (TorusLumps.parentBlock R.params.side z)
          (TorusLumps.parentBlock R.params.side z) m →
        (∀ (W W' : TorusFields.TorusField (n * R.params.side)) (Y Y' : Finset (TorusFields.TorusSite (n * R.params.side)))
            (ω : Y → R.labels.Ω) (ω' : Y' → R.labels.Ω) (k : ℕ),
          WeightedResponses.IsLiveState R.params R.coupling R.labelWeight W Y ω →
          WeightedResponses.IsLiveState R.params R.coupling R.labelWeight W' Y' ω' →
          ρ + (TorusLumps.clusterRange R.coupling : ℝ) / 64 ≤ k → k ≤ R.params.side * m - R.params.side →
          TorusLumps.StatesAgreeNear R.params W W' Y Y' ω ω' z z k →
          |Q W Y ω - Q' W' Y' ω'| ≤ K * Real.exp (-R.params.decayRate * (k - ρ))) →
        |StateLaws.settingMean s Q - StateLaws.settingMean s' Q'| ≤
          4 * K * Real.exp (-(R.params.rt * m / 2 ^ 4))
end YangMills.Construction.MomentLaw
end
