import YangMills.Construction.HoleBesideASecondHole.CutsLumpsBasesAndContours
import Mathlib
set_option autoImplicit false
noncomputable section
open scoped Quaternion
namespace YangMills.Construction.QuaternionLog
open YangMills.Construction.BlockAverages YangMills.Construction.LumpContours
def MinimalLogAnalyticNearOne : Prop :=
  ∃ Lg : ℍ[ℝ] → ℍ[ℝ], AnalyticOnNhd ℝ Lg (Metric.ball 1 1) ∧
    ∀ g : UnitQuaternion, ‖(g : ℍ[ℝ]) - 1‖ < 1 → ((minimalLog g : imaginaryQuaternions) : ℍ[ℝ]) = Lg g
end YangMills.Construction.QuaternionLog
end
