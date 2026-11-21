import YangMills.Construction.HullsInEveryVolume.HullDefs
import YangMills.Construction.HullsInEveryVolume.TiltDefs
import Mathlib
set_option autoImplicit false
noncomputable section
open MeasureTheory
namespace YangMills.Construction.MomentLaw
open TorusFields WeightedResponses HullTrees TorusLimits RenormalizationStepParameters
def severalLongHullClassesStatement : Prop :=
  EventuallyInParameters fun Tb _ y => ∀ (g β : ℝ) (K m : ℕ) (T : StageTower (Tb.stepParameters y)) (u n : ℕ)
    [NeZero n], HullChainAtLevel Tb y g β K m T u n →
    ∀ (q : ℕ) (zs : Fin q → TorusSite n) (D : ℝ), 1 ≤ q → 0 ≤ D →
      (∀ c e, c ≠ e → 83 * stageRange T u * keptSitesAlong D (stageRange T u) ≤ supDist (zs c) (zs e)) →
      (markedSampleLaw T β u n).real {w | ∀ e, zs e ∈ hullSet T u n w ∧
          D ≤ (supDiam (hullClass (stageRange T u) (hullSet T u n w) (zs e)) : ℝ)} ≤
        Real.exp (-(hullDecayRate Tb * stageCoupling T u * (1 + D / (stageRange T u : ℝ)))) ^ q
end YangMills.Construction.MomentLaw
end
