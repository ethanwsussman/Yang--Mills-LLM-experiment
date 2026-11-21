import YangMills.Construction.ClusterExpansionOfAStep.GasOfASetting
import YangMills.Construction.ClusterExpansionOfAStep.SharesOfHoledFieldsForget
import Mathlib
set_option autoImplicit false
noncomputable section
namespace YangMills.Construction
namespace StepGas
open TorusFields StepSettings HoledShares
variable (R : StepSetup) {n : ℕ} [NeZero n]
def emptyCoarseState : CoarseState R n := ⟨∅, fun z => absurd z.2 (Finset.notMem_empty _)⟩
def hotCaseGround (V : TorusField n) (q : CoarseState R n) : GasGround R n :=
  ⟨coldRegion R.params V, hotCoreSites R V, V, q⟩
def coldCaseGround (V : TorusField n) : GasGround R n := ⟨Finset.univ, ∅, V, emptyCoarseState R⟩
end StepGas
end YangMills.Construction
end
