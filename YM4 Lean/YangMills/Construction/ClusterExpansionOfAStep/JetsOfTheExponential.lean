import YangMills.Construction.ColdChainAtEveryLevel.LevelsAndFields
import Mathlib
set_option autoImplicit false
noncomputable section
open scoped Quaternion
namespace YangMills.Construction.QuaternionExponential
open YangMills.Construction.BlockAverages
def IteratedDerivBounded : Prop :=
  ∀ j : ℕ, ∃ C : ℝ, 0 ≤ C ∧ ∀ v : imaginaryQuaternions,
    ‖iteratedFDeriv ℝ j (fun w : imaginaryQuaternions => NormedSpace.exp (w : ℍ[ℝ])) v‖ ≤ C
end YangMills.Construction.QuaternionExponential
end
