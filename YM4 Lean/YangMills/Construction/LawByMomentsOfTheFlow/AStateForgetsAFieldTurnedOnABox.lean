import YangMills.Construction.LawByMomentsOfTheFlow.WindowOfTheLaw
import YangMills.Construction.ResponseInTheExpansion.FreeCoresOfAStepAreRare
import Mathlib
set_option autoImplicit false
noncomputable section
open MeasureTheory
namespace YangMills.Construction.MomentLaw
structure ReadsGaugeInvariantly {n : ℕ} [NeZero n] (A : Finset (TorusFields.TorusSite n)) (M : ℝ)
    (f : TorusFields.TorusField n → Finset (TorusFields.TorusSite n) → ℝ) : Prop where
  abs_le : ∀ W Yt, |f W Yt| ≤ M
  measurable : ∀ Yt, Measurable fun W => f W Yt
  gauge_invariant : ∀ g W Yt, f (TorusFields.gaugeTransform g W) Yt = f W Yt
  depends : ∀ W W' Yt Yt', (∀ c : TorusFields.TorusBond n, c.1 ∈ A → c.1 + TorusFields.unitStep n c.2 ∈ A →
      W c.1 c.2 = W' c.1 c.2) → Yt ∩ A = Yt' ∩ A → f W Yt = f W' Yt'
def forgetsRotatedFieldAt (T : RenormalizationStepParameters.ParameterAssignment) (y : ℝ) : Prop :=
  ∀ R : StepSettings.StepSetup, R.OnParameters T y → R.IsWellPosed → R.nextCoupling ≤ 1.01 * R.coupling →
    ∀ (n m : ℕ) [NeZero n] [NeZero (4 * m)] (V U : TorusFields.TorusField n)
      (q : StepSettings.CoarseState R n) (o : TorusFields.TorusSite n)
      (g : TorusFields.TorusSite n → BlockAverages.UnitQuaternion),
      TorusLumps.IsBlockTorusSide R.params n → TorusLumps.IsHullState R.params R.nextRange V q.1 →
      (∀ X ∈ TorusLumps.chainComponents R.nextRange q.1, StepSettings.coarseFactor V q X ≠ 0) →
      2 ^ 12 * R.range ≤ m → 8 * m ≤ n → Disjoint q.1 (ResponseInTheExpansion.supBall o m) →
      TorusFields.IsCold R.params.threshold U →
      (∀ c : TorusFields.TorusBond n, c.1 ∈ ResponseInTheExpansion.supBall o m →
        c.1 + TorusFields.unitStep n c.2 ∈ ResponseInTheExpansion.supBall o m →
        U c.1 c.2 = ResponseInTheExpansion.gaugeTransform g V c) →
      ∀ (A : Finset (TorusFields.TorusSite (n * R.params.side))) (M : ℝ)
        (f : TorusFields.TorusField (n * R.params.side) → Finset (TorusFields.TorusSite (n * R.params.side)) → ℝ),
        (∀ z ∈ A, TorusFields.supDist z (StepSettings.fineSite R.params.side o 0 0) + 1 + R.params.side ≤
          R.params.side * (m / 8)) → ReadsGaugeInvariantly A M f →
        |WeightedResponses.caseMean R (StepSettings.hotCoreSites R V) V q (fun W Yt _ _ _ => f W Yt) -
            coldExpectation R U (fun η => f ((coldSettingOver R U).field η) ∅)| ≤
          4 * M * Real.exp (-(T.rt * ((m - R.frameReach - 1 : ℕ) : ℝ) / 2 ^ 3)) +
            2 * M * (ResponseInTheExpansion.blocksNearFreeCores R.params.side R.range (ResponseInTheExpansion.supBall o m)).card *
              Real.exp (-(7 * T.gasRate * R.coupling))
def forgetsRotatedFieldStatement : Prop :=
  ∃ rt₀ : RenormalizationStepParameters.ChainParameters → ℝ, (∀ c, 0 < rt₀ c) ∧ ∀ T : RenormalizationStepParameters.ParameterAssignment, T.Admissible →
    T.ColdStepHolds → T.HoldsFrom WeightedResponses.ColdRegimeEstimatesAt →
    T.rt ≤ rt₀ T.toChainParameters → ∃ y₀ : ℝ, ∀ y : ℝ, y₀ ≤ y → forgetsRotatedFieldAt T y
end YangMills.Construction.MomentLaw
end
