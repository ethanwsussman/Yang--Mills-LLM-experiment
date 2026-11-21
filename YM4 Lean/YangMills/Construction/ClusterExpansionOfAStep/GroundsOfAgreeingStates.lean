import YangMills.Construction.ClusterExpansionOfAStep.FactorsOfAStep
import YangMills.Construction.ClusterExpansionOfAStep.GroundsOfAStep
import Mathlib
set_option autoImplicit false
noncomputable section
namespace YangMills.Construction
open TorusFields TorusLumps StepSettings
namespace StepGas
def GroundsAgreeNearOfStatesAgreeNear : Prop :=
  ∀ (R : StepSetup) (n n' : ℕ) [NeZero n] [NeZero n'] (V : TorusField n) (V' : TorusField n')
    (Y : Finset (TorusSite n)) (ω : Y → CoarseLabel R.labels.Ω R.params.side) (y : TorusSite n)
    (y' : TorusSite n') (m : ℕ),
    R.params.Admissible → 2 ^ 16 ≤ R.nextRange → R.params.side ∣ n → IsHullState R.params R.nextRange V Y →
    (∀ X ∈ chainComponents R.nextRange Y, coarseFactor V ⟨Y, ω⟩ X ≠ 0) →
    (∀ (Y' : Finset (TorusSite n')) (ω' : Y' → CoarseLabel R.labels.Ω R.params.side), R.params.side ∣ n' →
      IsHullState R.params R.nextRange V' Y' →
      (∀ X ∈ chainComponents R.nextRange Y', coarseFactor V' ⟨Y', ω'⟩ X ≠ 0) →
      StatesAgreeNear R.params V V' Y Y' ω ω' y y' m →
      GroundsAgreeNear (hotCaseGround R V ⟨Y, ω⟩) (hotCaseGround R V' ⟨Y', ω'⟩) y y' m) ∧
    (∀ ω' : (∅ : Finset (TorusSite n')) → CoarseLabel R.labels.Ω R.params.side,
      StatesAgreeNear R.params V V' Y ∅ ω ω' y y' m →
      GroundsAgreeNear (hotCaseGround R V ⟨Y, ω⟩) (coldCaseGround R V') y y' m)
end StepGas
end YangMills.Construction
end
