import YangMills.Construction.ConfigurationSpace.WhitneyPiecesCubesConstants
import Mathlib
set_option autoImplicit false
noncomputable section
namespace YangMills.Construction.ConfigurationSpace
open MeasureTheory
def TupleEuclideanBallVolume : Prop :=
  ∀ (J : Type) [Fintype J], 1 ≤ Fintype.card J → ∀ R : ℝ, 0 < R →
    volume {y : J → Fin 4 → ℝ | Real.sqrt (∑ a, ∑ c, y a c ^ 2) ≤ R} =
      ENNReal.ofReal (unitBallVol (4 * Fintype.card J) * R ^ (4 * Fintype.card J))
end YangMills.Construction.ConfigurationSpace
end
