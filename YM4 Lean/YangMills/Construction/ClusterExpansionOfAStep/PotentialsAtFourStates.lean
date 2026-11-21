import YangMills.Construction.ClusterExpansionOfAStep.FourCorners
import YangMills.Construction.ClusterExpansionOfAStep.PotentialOfASetting
import Mathlib
set_option autoImplicit false
noncomputable section
open MeasureTheory
namespace YangMills.Construction.StepSettings
open BlockAverages LumpContours TorusFields TorusLumps RenormalizationStepParameters ClusterExpansionOfAStep
def potentialMixedDifferenceBound : Prop :=
  ∀ T : ParameterAssignment, T.Admissible → ∃ C y₀ : ℝ, ∀ y : ℝ, y₀ ≤ y → ∀ R : StepSetup, R.params = T.stepParameters y →
    R.anchorRadius = T.ρA → y ≤ R.coupling → R.HasExpansions → ∀ (n : ℕ) [NeZero n], T.n₀ ≤ n →
      ∀ (s : Fin 2 → Fin 2 → ChartSetting R n) (η : ∀ i j, FreeCoords (s i j).free)
        (P P' : Finset (TorusSite (n * R.params.side))) (d : ℕ),
        (∀ i j, (s i j).IsAdmissible) → (∀ i j, (s i j).InBalls (η i j)) →
        FourCornerStates P P' (fun i j => (s i j).field (η i j)) (fun i j => (s i j).support)
          (fun i j => (s i j).labelling) →
        (∀ z ∈ P, ∀ z' ∈ P', d ≤ supDist z z') → (R.range : ℝ) / 16 ≤ d →
        (∀ i j, ∀ X ∈ chainComponents R.range (s i j).support,
          ¬ ((X ∩ thickening R.range P).Nonempty ∧ (X ∩ thickening R.range P').Nonempty)) →
        (s 1 1).kernelProduct (η 1 1) * (s 0 0).kernelProduct (η 0 0) =
          (s 1 0).kernelProduct (η 1 0) * (s 0 1).kernelProduct (η 0 1) →
        (s 1 1).haarJacobian (η 1 1) * (s 0 0).haarJacobian (η 0 0) =
          (s 1 0).haarJacobian (η 1 0) * (s 0 1).haarJacobian (η 0 1) →
        |(s 1 1).potential (η 1 1) + (s 0 0).potential (η 0 0) - (s 1 0).potential (η 1 0) -
            (s 0 1).potential (η 0 1)| ≤
          C * R.coupling * min (P.card : ℝ) P'.card * Real.exp (-(R.params.decayRate * d / 3))
end YangMills.Construction.StepSettings
end
