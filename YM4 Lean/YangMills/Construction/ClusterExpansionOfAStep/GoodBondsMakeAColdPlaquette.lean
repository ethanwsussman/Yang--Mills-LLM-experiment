import YangMills.Construction.ClusterExpansionOfAStep.ConstantsOfTheColdChain
import YangMills.Construction.ClusterExpansionOfAStep.MarksOfAStep
import Mathlib
set_option autoImplicit false
noncomputable section
open scoped Quaternion
namespace YangMills.Construction.StepFrames
def coldPlaquette_of_small_frameDeviation : Prop :=
  ∀ (p : TorusLumps.StepParameters) (δ lam ρA σA cg : ℝ) (N : ℕ → ℝ), p.Admissible →
    ColdChain.ColdChainConstants p.coupling δ p.side lam ρA σA cg N →
    2 * p.threshold ≤ σA →
    ∀ (t r r' n : ℕ) [NeZero n] (V : TorusFields.TorusField n) (S C : Finset (TorusFields.TorusSite n)) (s : ℝ),
      StepMarks.RangesAdmissible r r' →
      StepMarks.IsStepSituation p r' V S C s →
      N 0 * s * Real.exp (-(δ * ((r / 2 ^ 11 : ℕ) : ℝ))) ≤ p.threshold / 128 →
      ∀ (W : TorusFields.TorusField (n * p.side)) (x : TorusFields.TorusSite (n * p.side)) (μ ν : Fin 4), μ < ν →
        (∀ z ∈ TorusFields.plaquetteVertices x μ ν, TorusLumps.parentBlock p.side z ∉ C) →
        (∀ e ∈ StepCosts.chartBonds p.side n,
          (∃ z ∈ TorusFields.plaquetteVertices x μ ν, TorusLumps.parentBlock p.side e.1 = TorusLumps.parentBlock p.side z) →
          ‖(StepMarks.frameDeviation p ρA t (r / 2 ^ 11) V W e : ℍ[ℝ])‖ ≤ p.threshold / 64) →
        TorusFields.curvature W x μ ν < p.threshold / 4
end YangMills.Construction.StepFrames
end
