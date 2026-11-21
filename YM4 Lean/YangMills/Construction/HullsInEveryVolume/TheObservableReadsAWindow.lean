import YangMills.Construction.HullsInEveryVolume.LimitDefs
import YangMills.Construction.HullsInEveryVolume.TwoPointLawDefs
import YangMills.Construction.ResponseInTheExpansion.CurvatureOnTheBareTorus
import Mathlib
set_option autoImplicit false
noncomputable section
open MeasureTheory Filter
open scoped Topology
namespace YangMills.Construction.HullsInEveryVolume
def observableReadsWindowStatement : Prop :=
  ∀ (L K : ℕ) [NeZero L] (f : (Fin 4 → ℝ) → ℝ), Odd L → 1 < L → HasCompactSupport f →
    ∃ (R : ℕ) (G : TorusLimits.WindowValuation R → ℝ), TorusLimits.IsBoundedWindowObservable G ∧
      Measurable (fun U : TorusLimits.FineField L K => TorusLimits.evalOnField G U) ∧
      (∀ U : TorusLimits.FineField L K, InfiniteLattice.smearedEnergy f U = TorusLimits.evalOnField G U) ∧
      ∀ᶠ m in atTop, ∀ W : TorusFields.TorusField (WeightedResponses.fineSide L K (2 * L ^ m)),
        WeightedResponses.curvatureObservable (TwoPointLaw.scaledTestWeight L K K f 0 _) W = TorusLimits.evalOnTorus G W
end YangMills.Construction.HullsInEveryVolume
end
