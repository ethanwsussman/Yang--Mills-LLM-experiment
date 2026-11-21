import YangMills.Construction.LawByMomentsOfTheFlow.ObservablesCompletedByScores
import Mathlib
set_option autoImplicit false
noncomputable section
namespace YangMills.Construction.FreeEnergies
open YangMills.Construction.TorusLumps YangMills.Construction.TorusFields YangMills.Construction.WeightedResponses
def completedObservablesBounded : Prop :=
  ∀ (ℓ : StepParameters), ℓ.Admissible → ∀ (T : StageTower ℓ) (al : ℕ → ℝ) (s n : ℕ) [NeZero n],
    (∀ h : PlaquetteWeight (fineSide ℓ.side s n), Measurable (completedObservable T al s n h) ∧
      ∃ C : ℝ, ∀ u, |completedObservable T al s n h u| ≤ C) ∧
    (∀ h : PlaquetteWeight (fineSide ℓ.side (s + 1) n), Measurable (sourceTerm T al s n h) ∧
      ∃ C : ℝ, ∀ u, |sourceTerm T al s n h u| ≤ C) ∧
    ∀ (x a : ℝ) (h : PlaquetteWeight (fineSide ℓ.side (s + 1) n)),
      Measurable fun p : TorusField (n * ℓ.side) × StepOutcome ℓ n => stepSourceTerm ℓ x a s h p.1 p.2
end YangMills.Construction.FreeEnergies
end
