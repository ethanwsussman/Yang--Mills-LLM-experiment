import YangMills.Construction.ClusterExpansionOfAStep.FreeClassesOfAStep
import YangMills.Construction.ResponseInTheExpansion.PairsAtALevel
import Mathlib
set_option autoImplicit false
noncomputable section
open MeasureTheory
namespace YangMills.Construction.CellWindows
def sqrtClusterWeightTailAtBlockStatement : Prop :=
  WeightedResponses.HoldsAtAdmissibleParameters fun Tb y => ∀ x : ℝ, y ≤ x →
    ∀ (n : ℕ) [NeZero n] (Y : TorusFields.TorusSite n) (ν : ℕ),
    (open Classical in
      ∑ θ ∈ (TorusLumps.supportsAtBlock (Tb.stepParameters y).side
          (TorusLumps.clusterRange x) Y).filter
          (fun θ => ν ≤ TorusLumps.supportUnitCount (Tb.stepParameters y).side
            (TorusLumps.clusterRange x) θ),
        Real.sqrt (TorusLumps.clusterWeight (Tb.stepParameters y).side Tb.gasRate x
          (TorusLumps.clusterRange x) θ)) ≤
      2 * Real.exp (-(7 * Tb.gasRate * x * ν))
end YangMills.Construction.CellWindows
end
