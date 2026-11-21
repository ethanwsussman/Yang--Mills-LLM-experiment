import YangMills.Construction.RunningCouplingSlope.FamiliesOfExponents
import Mathlib
set_option autoImplicit false
noncomputable section
namespace YangMills.Construction.LaplaceAsymptotics
open ColdStepAtMirrorFrames
def LogCutoffIntegralContDiffTwo : Prop :=
  ∀ (ι : Type) [Fintype ι] [DecidableEq ι] (k : ℕ) (ρ x : ℝ) (p : ℝ → ℝ)
    (Q B : (Fin k → ℝ) × BondField ι → ℝ), 0 < ρ → IsCutoff ρ p →
    (∀ η : BondField ι, (∀ b, ‖η b‖ ≤ ρ) → ContDiffAt ℝ 3 Q (0, η)) →
    (∀ η : BondField ι, (∀ b, ‖η b‖ ≤ ρ) → ContDiffAt ℝ 3 B (0, η)) →
    ContDiffAt ℝ 2 (logCutoffIntegral ρ p x Q B) 0
end YangMills.Construction.LaplaceAsymptotics
end
