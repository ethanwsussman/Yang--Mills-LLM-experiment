import YangMills.Construction.ConfigurationSpace.WhitneyPiecesCubesConstants
import Mathlib
set_option autoImplicit false
noncomputable section
namespace YangMills.Construction.ConfigurationSpace
open MeasureTheory
def DiagonalTubeVolumeBound : Prop :=
  ∀ (n : ℕ) (a b : Fin n), a ≠ b → ∀ s R : ℝ, 0 ≤ s → 0 < R →
    volume {x : Config n | maxNorm (x a - x b) ≤ s ∧ configNorm x ≤ R} ≤
      ENNReal.ofReal ((2 * s) ^ 4 * unitBallVol (4 * n - 4) * R ^ (4 * n - 4))
end YangMills.Construction.ConfigurationSpace
end
