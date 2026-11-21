import YangMills.Construction.ClusterExpansionOfAStep.ClassesOfTwoGrounds
import YangMills.Construction.ClusterExpansionOfAStep.StepAtFixedParameters
import Mathlib
set_option autoImplicit false
noncomputable section
open MeasureTheory
namespace YangMills.Construction.ClusterExpansionOfAStep
open RenormalizationStepParameters StepSettings StepGas TorusFields TorusLumps
def AllowedStatesTransferInBox : Prop :=
  ∀ T : ParameterAssignment, T.Admissible → ∃ y₀ : ℝ, ∀ y : ℝ, y₀ ≤ y → ∀ R : StepSetup, R.OnParameters T y →
    R.nextCoupling ≤ 1.01 * R.coupling →
    ∀ (n n' : ℕ) [NeZero n] [NeZero n'] (G : GasGround R n) (G' : GasGround R n') (Y : TorusSite n)
      (Y' : TorusSite n') (N : ℕ) (i : G.GasSpin) (i' : G'.GasSpin) (s : SupportState i.1) (s' : SupportState i'.1),
      G.IsAdmissibleGround → G'.IsAdmissibleGround → 16 * R.frameReach ≤ N → GroundsAgreeNear G G' Y Y' N →
      (∀ y ∈ i.1.core, ∃ h, OffsetInBox (N - R.frameReach - 1) h ∧ y = Y + siteOfInt h) →
      (∀ y ∈ i'.1.core, ∃ h, OffsetInBox (N - R.frameReach - 1) h ∧ y = Y' + siteOfInt h) →
      SameSupportNear i.1 i'.1 Y Y' N →
      (∀ h, OffsetInBox N h → (Y + siteOfInt h ∈ i.1.core ↔ Y' + siteOfInt h ∈ i'.1.core)) →
      SameStateNear i.1 i'.1 s s' Y Y' N →
      G.IsAllowed i.1 s → G'.IsAllowed i'.1 s' ∧ G.activity i.1 s = G'.activity i'.1 s'
end YangMills.Construction.ClusterExpansionOfAStep
end
