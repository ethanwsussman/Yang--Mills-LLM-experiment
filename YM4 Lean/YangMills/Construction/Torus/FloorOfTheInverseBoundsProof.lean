import YangMills.Construction.Torus.FloorOfTheInverseBounds
import YangMills.Construction.Torus.WeightedDistanceAndCellsOfASeparatedSequence
import Mathlib
set_option autoImplicit false
noncomputable section
namespace YangMills.Construction.GeneralTorus.InverseBounds
open YangMills.Construction.SeparatedSequences YangMills.Construction.GeneralTorus.GreenBounds
theorem inverseDecayRate_pos {L : ℕ} (hL : 0 < L) {δ C : ℝ} (hδ : 0 < δ) (hC : 0 < C) :
    0 < SeparatedSequences.inverseDecayRate 4 L δ C := by
  have hγ : 0 < SeparatedSequences.compressedGreenLowerBound 4 1 := by
    unfold SeparatedSequences.compressedGreenLowerBound SeparatedSequences.testFormEnergyConstant
    positivity
  have hZ : 0 < SeparatedSequences.compressedEntryConstant 4 L δ C := by
    unfold SeparatedSequences.compressedEntryConstant SeparatedSequences.greenColumnConstant
    positivity
  have hc : 0 < SeparatedSequences.expSumConstant 4 L (δ / 2) := by
    unfold SeparatedSequences.expSumConstant
    positivity
  unfold SeparatedSequences.inverseDecayRate
  refine lt_min (by positivity) ?_
  positivity
theorem decayRateOfInverse_pos {L : ℕ} (hL : Blocking.DimFourOddBlockingFactorGeThirteen 4 L)
    (hw : (GreenBounds.chosen L).Valid L) : 0 < decayRateOfInverse L :=
  inverseDecayRate_pos (by have := hL.thirteen_le; omega) hw.rate_pos
    (lt_of_lt_of_le one_pos hw.one_le_bound)
end YangMills.Construction.GeneralTorus.InverseBounds
end
