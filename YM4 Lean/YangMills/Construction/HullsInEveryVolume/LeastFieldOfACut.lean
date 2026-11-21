import YangMills.Construction.ClusterExpansionOfAStep.MarksOfAStep
import YangMills.Construction.ClusterExpansionOfAStep.ShareOfAChainSplits
import Mathlib
set_option autoImplicit false
noncomputable section
namespace YangMills.Construction.HullsInEveryVolume
def minimizingFieldOfCutoff : Prop :=
  ∀ (ℓ : TorusLumps.StepParameters) (δ lam ρA σA cg : ℝ) (N : ℕ → ℝ), ℓ.Admissible →
    ColdChain.ColdChainConstants ℓ.coupling δ ℓ.side lam ρA σA cg N →
    2 * ℓ.threshold ≤ σA → ∀ (t r' n : ℕ) [NeZero n] (V : TorusFields.TorusField n)
      (S C : Finset (TorusFields.TorusSite n)) (s : ℝ),
      StepMarks.IsStepSituation ℓ r' V S C s →
      LumpContours.IsMinimizingField ℓ.coupling
        (TorusFields.cellsOfSites (TorusFields.torusFrame ℓ.side t n) S)
        (TorusFields.readAtLevel (TorusFields.torusFrame ℓ.side t n) (TorusFields.torusFrame ℓ.side t n).top V)
        (TorusFields.readAtLevel (TorusFields.torusFrame ℓ.side t n) (TorusFields.torusFrame ℓ.side t n).depth
          (ClusterExpansionOfAStep.minimizingField ℓ.coupling ρA ℓ.side t S V)) ∧
      ∀ b : TorusFields.TorusBond (n * ℓ.side),
        StepCosts.chartCoord ℓ V (ClusterExpansionOfAStep.minimizingField ℓ.coupling ρA ℓ.side t S V) b =
          StepMarks.minimizerCoord ℓ.coupling ρA ℓ.side t S V b
end YangMills.Construction.HullsInEveryVolume
end
