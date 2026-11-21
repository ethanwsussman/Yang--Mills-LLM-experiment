import YangMills.Construction.ColdChainAtEveryLevel.LevelsAndFields
import Mathlib
set_option autoImplicit false
noncomputable section
open scoped Quaternion Topology
namespace YangMills.Construction.BlockAverages
def ExpShiftCurve : Prop :=
  ∃ K ρ₀ : ℝ, 0 < K ∧ 0 < ρ₀ ∧ ∀ v e : imaginaryQuaternions, ‖v‖ ≤ ρ₀ →
    ∃ η : ℝ → imaginaryQuaternions, AnalyticAt ℝ η 0 ∧ η 0 = 0 ∧
    (∀ᶠ τ : ℝ in 𝓝 0, expUnit (η τ) * expUnit v = expUnit (v + τ • e)) ∧
    ‖deriv η 0 - e‖ ≤ K * ‖v‖ * ‖e‖ ∧ ‖deriv (deriv η) 0‖ ≤ K * ‖e‖ ^ 2
end YangMills.Construction.BlockAverages
end
