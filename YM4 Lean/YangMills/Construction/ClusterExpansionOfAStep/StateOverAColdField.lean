import YangMills.Construction.ClusterExpansionOfAStep.FactorsOfAStep
import Mathlib
set_option autoImplicit false
noncomputable section
open MeasureTheory
namespace YangMills.Construction
namespace StepSettings
open TorusFields TorusLumps
def coldFieldStateStatement : Prop :=
  ∀ R : StepSetup, R.IsWellPosed → ∀ (n : ℕ) [NeZero n], R.params.n₀ ≤ n →
    (∀ (V : TorusField n) (ω : (∅ : Finset (TorusSite n)) → CoarseLabel R.labels.Ω R.params.side),
      coarseStateWeight R ∅ V ⟨∅, ω⟩ = kernelImage R.params R.coupling R.functional n V) ∧
    (IsBlockTorusSide R.params n → ∀ V : TorusField n, IsCold R.params.threshold V →
      hotCoreSites R V = ∅ ∧ ∀ Y : Finset (TorusSite n), IsHullState R.params R.nextRange V Y ↔ Y = ∅)
end StepSettings
end YangMills.Construction
end
