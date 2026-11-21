import YangMills.Construction.LawOnABoxOfTheFlow.EventsOfABox
import YangMills.Construction.ResponseInTheExpansion.PairsAtALevel
import Mathlib
set_option autoImplicit false
noncomputable section
open MeasureTheory ProbabilityTheory
open scoped Quaternion
namespace YangMills.Construction.BoxEvents
def conditionalDensityStatement : Prop :=
  WeightedResponses.HoldsAtAdmissibleParameters fun Tb y => ∀ κ₀ : ℝ, 1 / 27 ≤ κ₀ → κ₀ ≤ 1 / 21 →
    ∀ C₁ : ℝ, ∃ c xs : ℝ, 0 < c ∧
    ∀ (T : WeightedResponses.StageTower (Tb.stepParameters y)) (β : ℝ) (k n : ℕ) [NeZero n]
      (o : TorusFields.TorusSite n) (x : ℝ) (R : ℕ),
      IsBoxDatum Tb y T β κ₀ xs k n → x = flowCoupling (Tb.stepParameters y) β k →
      R = BoxGaussian.boxRadius κ₀ x →
      ∀ (W W' : TorusFields.TorusField n) (Y : Finset (TorusFields.TorusSite n)) (ω : Y → (T.stage k).labels.Ω),
        BoxGaussian.restrictOuter o R W = BoxGaussian.restrictOuter o R W' →
        Disjoint Y (ResponseInTheExpansion.supBall o (3 * R)) →
        (∀ p ∈ TorusFields.plaquettesIn (ResponseInTheExpansion.supBall o (2 * R)),
          TorusFields.curvature W p.1 p.2.1 p.2.2 ≤ C₁ * (R : ℝ) ^ 2 * BoxGaussian.boxScale x) →
        (∀ p ∈ TorusFields.plaquettesIn (ResponseInTheExpansion.supBall o (2 * R)),
          TorusFields.curvature W' p.1 p.2.1 p.2.2 ≤ C₁ * (R : ℝ) ^ 2 * BoxGaussian.boxScale x) →
        TorusLumps.IsHullState (Tb.stepParameters y) (TorusLumps.clusterRange x) W Y →
        0 < (T.stage k).labelWeight n W Y ω →
        TorusLumps.IsHullState (Tb.stepParameters y) (TorusLumps.clusterRange x) W' Y ∧
          0 < (T.stage k).labelWeight n W' Y ω ∧
          |Real.log ((T.stage k).labelWeight n W' Y ω) - Real.log ((T.stage k).labelWeight n W Y ω) +
              x * (TorusFields.actionAtLevel Tb.coupling Tb.side k (ResponseInTheExpansion.supBall o (2 * R)) W' -
                TorusFields.actionAtLevel Tb.coupling Tb.side k (ResponseInTheExpansion.supBall o (2 * R)) W) -
              (mirrorSum (T.stage k).density o R id W' - mirrorSum (T.stage k).density o R id W)| ≤
            Real.exp (-(c * R))
end YangMills.Construction.BoxEvents
end
