import YangMills.Construction.FreeEnergiesOfTheFlow.SupportsOverAStepDefs
import Mathlib
set_option autoImplicit false
noncomputable section
open MeasureTheory
namespace YangMills.Construction.FreeEnergies
def supportResponseLocalityStatement : Prop :=
  WeightedResponses.HoldsAtEveryStep fun _ R A => ∀ (n : ℕ) [NeZero n] (s : StepSettings.ChartSetting R n),
    R.params.n₀ ≤ n → s.IsAdmissible →
    (∀ η, s.InBalls η → WeightedResponses.IsLiveState R.params R.coupling R.labelWeight (s.field η) s.support s.labelling ∧
      s.bases ∈ TorusLumps.baseChoices R.params
        (TorusFields.readAtLevel (TorusLumps.stepBlockFrame R.params.side n) 0 (s.field η))) ∧
    ∀ (f : WeightedResponses.PlaquetteWeight (WeightedResponses.fineSide R.params.side (R.depth + 1) n)) (k : ℕ)
      (bad : Finset (TorusFields.TorusBond (n * R.params.side))),
      WeightedResponses.weightNorm R.params.side R.depth f ≤ 1 → R.range ≤ k → 4 ≤ k →
      2 * k + 2 < n → ∀ η η', s.InBalls η → s.InBalls η' →
      (∀ b : s.free, (∃ Y ∈ upperSites f, TorusFields.supDist (StepSettings.bondBlock (R := R) b.1) Y ≤ k) → η b = η' b) →
      |ResponseInTheExpansion.centeredSupportResponse A s.coarse f (s.field η) s.support s.labelling bad s.bases -
          ResponseInTheExpansion.centeredSupportResponse A s.coarse f (s.field η') s.support s.labelling bad s.bases| ≤
        lowerSizeConst A f * ResponseInTheExpansion.meanSiteScore A.score (lowerSites f) s.support s.labelling *
          Real.exp (-(8 * R.params.rt * k))
end YangMills.Construction.FreeEnergies
end
