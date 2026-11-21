import YangMills.Construction.ConfigurationSpace.WhitneyPiecesCubesConstants
import Mathlib
set_option autoImplicit false
noncomputable section
namespace YangMills.Construction.ConfigurationSpace
open WhitneyScales MeasureTheory
open scoped ENNReal
def CenterCountByVolume : Prop :=
  ∀ (n j : ℕ) (S : Set (IntPoint n)) (U : Set (Config n)),
    (∀ z ∈ S, translateSet (pieceCenter j z)
      {x | ∀ k, coords x k ∈ Set.Ioo (-(1 / 4 * whitneySide j)) (1 / 4 * whitneySide j)} ⊆ U) →
    (setCard S : ℝ≥0∞) ≤ ENNReal.ofReal ((2 / whitneySide j) ^ (4 * n)) * volume U
end YangMills.Construction.ConfigurationSpace
end
