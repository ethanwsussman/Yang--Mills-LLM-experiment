import YangMills.Construction.ResponseInTheExpansion.ResponseInASetting
import YangMills.Construction.ResponseInTheExpansion.SupportsAlongTheLevels
import Mathlib
set_option autoImplicit false
noncomputable section
open MeasureTheory
namespace YangMills.Construction.ResponseInTheExpansion
def stageMassPositive : Prop :=
  WeightedResponses.HoldsAtEveryStep fun _ R _ => ∀ (n : ℕ) [NeZero n], TorusLumps.IsBlockTorusSide R.params n →
    0 < stateIntegral R n (fun _ _ _ => 1) ∧
      ENNReal.ofReal (stateIntegral R n fun _ _ _ => 1) = stateLIntegral R n fun _ _ _ => 1
end YangMills.Construction.ResponseInTheExpansion
end
