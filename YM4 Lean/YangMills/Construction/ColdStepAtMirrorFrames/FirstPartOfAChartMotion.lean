import YangMills.Construction.ColdChainAtEveryLevel.LevelsAndFields
import Mathlib
set_option autoImplicit false
noncomputable section
open YangMills.Construction.BlockAverages
namespace YangMills.Construction.ColdStepAtMirrorFrames
def ConjugatedExpFirstOrder : Prop :=
  ∃ C : ℝ, 0 ≤ C ∧ ∀ (p : ℕ) (α u v : (Fin p → ℝ) → imaginaryQuaternions) (e : Fin p → ℝ),
    ContDiffAt ℝ 1 α 0 → ContDiffAt ℝ 1 u 0 → ContDiffAt ℝ 1 v 0 → α 0 = 0 → v 0 = 0 → ‖u 0‖ ≤ 1 →
    (∀ᶠ τ in nhds 0, expUnit (α τ) = expUnit (u τ) * expUnit (v τ) * (expUnit (u 0))⁻¹) →
    ‖fderiv ℝ α 0 e - (fderiv ℝ u 0 e + fderiv ℝ v 0 e)‖ ≤
      C * ‖u 0‖ * (‖fderiv ℝ u 0 e‖ + ‖fderiv ℝ v 0 e‖)
end YangMills.Construction.ColdStepAtMirrorFrames
end
