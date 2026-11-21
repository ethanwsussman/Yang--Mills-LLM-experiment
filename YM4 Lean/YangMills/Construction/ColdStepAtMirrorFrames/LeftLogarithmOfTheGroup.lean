import YangMills.Construction.ColdChainAtEveryLevel.LevelsAndFields
import Mathlib
set_option autoImplicit false
noncomputable section
open scoped Quaternion Topology
namespace YangMills.Construction.ColdStepAtMirrorFrames
open YangMills.Construction.BlockAverages
def LeftLogarithmExists : Prop :=
  ∃ (Θ : imaginaryQuaternions × imaginaryQuaternions → imaginaryQuaternions) (C : ℝ), 0 < C ∧
    (∀ v : imaginaryQuaternions, ContDiffAt ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) Θ (v, 0)) ∧
    (∀ v : imaginaryQuaternions, Θ (v, 0) = 0) ∧
    (∀ v : imaginaryQuaternions, ∀ᶠ z in 𝓝 (0 : imaginaryQuaternions),
      expUnit (v + z) = expUnit (Θ (v, z)) * expUnit v) ∧
    ∀ (v : imaginaryQuaternions) (j : ℕ), ‖v‖ ≤ 1 → j ≤ 3 → ‖iteratedFDeriv ℝ j Θ (v, 0)‖ ≤ C
end YangMills.Construction.ColdStepAtMirrorFrames
end
