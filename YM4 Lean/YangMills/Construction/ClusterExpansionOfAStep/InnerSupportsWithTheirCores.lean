import YangMills.Construction.ClusterExpansionOfAStep.SharedGasOfTwoGrounds
import YangMills.Construction.ClusterExpansionOfAStep.StepAtFixedParameters
import Mathlib
set_option autoImplicit false
noncomputable section
open MeasureTheory
namespace YangMills.Construction.ClusterExpansionOfAStep
open Dobrushin RenormalizationStepParameters StepSettings StepGas TorusFields TorusLumps
def InnerSupportsCorrespondWithCores : Prop :=
  ∀ T : ParameterAssignment, T.Admissible → ∃ y₀ : ℝ, ∀ y : ℝ, y₀ ≤ y → ∀ R : StepSetup, R.OnParameters T y →
    ∀ (n n' : ℕ) [NeZero n] [NeZero n'] (G : GasGround R n) (G' : GasGround R n') (Y : TorusSite n)
      (Y' : TorusSite n') (N : ℕ) (A : Finset (TorusSite n)) (A' : Finset (TorusSite n')),
      16 * R.frameReach ≤ N → GroundsAgreeNear G G' Y Y' N → BlockSetsAgreeNear A A' Y Y' N →
      ∃ e : G.InnerSpin Y (N - R.frameReach - 1) A ≃ G'.InnerSpin Y' (N - R.frameReach - 1) A',
        ∀ j : G.InnerSpin Y (N - R.frameReach - 1) A,
          SameSupportNear j.1.1 (e j).1.1 Y Y' N ∧
            (∀ h, OffsetInBox N h → (Y + siteOfInt h ∈ j.1.1.core ↔ Y' + siteOfInt h ∈ (e j).1.1.core)) ∧
            (j.1.1.Meets Y ↔ (e j).1.1.Meets Y') ∧
            supportUnitCount R.params.side R.range j.1.1 = supportUnitCount R.params.side R.range (e j).1.1 ∧
            ∀ j' : G.InnerSpin Y (N - R.frameReach - 1) A, j ≠ j' →
              (j.1.1.FarApart j'.1.1 ↔ (e j).1.1.FarApart (e j').1.1)
end YangMills.Construction.ClusterExpansionOfAStep
end
