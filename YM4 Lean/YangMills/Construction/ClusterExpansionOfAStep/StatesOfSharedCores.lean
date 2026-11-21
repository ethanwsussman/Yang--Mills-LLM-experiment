import YangMills.Construction.ClusterExpansionOfAStep.ClassesOfTwoGrounds
import Mathlib
set_option autoImplicit false
noncomputable section
open MeasureTheory
namespace YangMills.Construction.ClusterExpansionOfAStep
open TorusFields StepSettings StepGas
def SharedCoreStatesEquiv : Prop :=
  ∀ (R : StepSetup) (n n' : ℕ) [NeZero n] [NeZero n'] (θ : GasSupport R n) (θ' : GasSupport R n')
    (Y : TorusSite n) (Y' : TorusSite n') (N : ℕ), Odd R.params.side → 2 * N + 2 < n → 2 * N + 2 < n' →
    SameSupportNear θ θ' Y Y' N →
    (∀ h, OffsetInBox N h → (Y + siteOfInt h ∈ θ.core ↔ Y' + siteOfInt h ∈ θ'.core)) →
    ∃ f : SupportState θ ≃ᵐ SupportState θ',
      MeasurePreserving f (supportStateMeasure θ) (supportStateMeasure θ') ∧
      ∀ s, SameStateNear θ θ' s (f s) Y Y' N
end YangMills.Construction.ClusterExpansionOfAStep
end
