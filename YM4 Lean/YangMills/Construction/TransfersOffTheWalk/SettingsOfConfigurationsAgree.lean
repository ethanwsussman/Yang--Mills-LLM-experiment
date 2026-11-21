import YangMills.Construction.ClusterExpansionOfAStep.GasOfASetting
import Mathlib
set_option autoImplicit false
noncomputable section
namespace YangMills.Construction
namespace StepSettings
open TorusFields StepGas
def LocalSettingsAgree : Prop :=
  ∀ (R : StepSetup) (n : ℕ) [NeZero n] (G : GasGround R n) (σ σ' : G.Config) (Y : TorusSite n) (m : ℕ),
    Odd R.params.side → 2 * m + 2 < n →
    (∀ i : G.GasSpin, (∃ h, OffsetInBox m h ∧ Y + siteOfInt h ∈ i.1.core) → σ i = σ' i) →
    SettingsAgreeNear (G.settingOf (G.familyOf σ)) (G.settingOf (G.familyOf σ')) Y Y m
end StepSettings
end YangMills.Construction
end
