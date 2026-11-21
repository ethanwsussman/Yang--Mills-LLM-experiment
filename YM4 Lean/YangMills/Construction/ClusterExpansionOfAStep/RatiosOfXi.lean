import YangMills.Construction.ClusterExpansionOfAStep.ColumnsOfTheGas
import Mathlib
set_option autoImplicit false
noncomputable section
open MeasureTheory
namespace YangMills.Construction
namespace ClusterExpansionOfAStep
open StepSettings StepGas Dobrushin
def PartitionRatioBounds : Prop :=
  ∀ (R : StepSetup) (n : ℕ) [NeZero n] (G : GasGround R n) (c : ℝ),
    (∀ off : G.GasSpin → Prop,
      ∃ h : G.pairConstraint.IsActivityBounded (G.referenceMeasureOff off) G.weight (G.spinActivity c),
        G.HasSmallColumns off c h) →
    (∀ Y, MeasurableSet (G.NoSpinMeets Y)) ∧ (∀ A, 0 < G.xi A) ∧ G.xi Finset.univ = 1 ∧
    (∀ A Y, (G.gibbsLaw A).real (G.NoSpinMeets Y) = G.xi (insert Y A) / G.xi A) ∧
    ∀ A Y, 1 - Real.exp (-(7 * c * R.coupling)) ≤ G.xi (insert Y A) / G.xi A ∧
      G.xi (insert Y A) / G.xi A ≤ 1
end ClusterExpansionOfAStep
end YangMills.Construction
end
