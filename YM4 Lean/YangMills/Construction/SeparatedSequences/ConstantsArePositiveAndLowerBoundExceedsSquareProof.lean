import YangMills.Construction.SeparatedSequences.ChosenConstantsOfTheConditions
import YangMills.Construction.Torus.FloorsOfTheAveragedSquareExpansionProof
import Mathlib
set_option autoImplicit false
noncomputable section
namespace YangMills.Construction.SeparatedClasses.OperatorConstantsPos
variable {L : ℕ}
theorem thirteen_le_cast (hL : Conventions.IsAdmissibleBlockingFactor L) : (13 : ℝ) ≤ (L : ℝ) := by
  exact_mod_cast hL.2
theorem cast_pos (hL : Conventions.IsAdmissibleBlockingFactor L) : (0 : ℝ) < (L : ℝ) := by
  have h := thirteen_le_cast hL
  linarith
theorem one_sub_inv_sq_pos (hL : Conventions.IsAdmissibleBlockingFactor L) :
    0 < 1 - ((L : ℝ) ^ 2)⁻¹ := by
  have h13 := thirteen_le_cast hL
  have h1 : (1 : ℝ) < (L : ℝ) ^ 2 := by nlinarith
  have h2 := inv_lt_one_of_one_lt₀ h1
  linarith
theorem greenDecayRate_pos (hL : Conventions.IsAdmissibleBlockingFactor L) :
    0 < Weighted.greenDecayRate 4 L := by
  have h := cast_pos hL
  unfold Weighted.greenDecayRate
  positivity
theorem latticeSumConst_pos (hL : Conventions.IsAdmissibleBlockingFactor L) {κ : ℝ} (hκ : 0 < κ) :
    0 < Weighted.latticeSumConst 4 L κ := by
  have h := cast_pos hL
  unfold Weighted.latticeSumConst
  positivity
theorem weightedBoundConst_pos (hL : Conventions.IsAdmissibleBlockingFactor L) :
    0 < Weighted.weightedBoundConst 4 L := by
  have h := cast_pos hL
  have hε := greenDecayRate_pos hL
  have hc : 0 < Weighted.coercivityConst L := one_sub_inv_sq_pos hL
  unfold Weighted.weightedBoundConst
  positivity
theorem upperBoundConst_pos (hL : Conventions.IsAdmissibleBlockingFactor L) :
    0 < Weighted.upperBoundConst 4 L := by
  have h := cast_pos hL
  have hε := greenDecayRate_pos hL
  have hw := weightedBoundConst_pos hL
  have hs := latticeSumConst_pos hL (κ := 1 / 4 * Weighted.greenDecayRate 4 L) (by positivity)
  unfold Weighted.upperBoundConst
  positivity
theorem lowerBoundConst_pos : 0 < Weighted.lowerBoundConst 4 := by apply _root_.YangMills.Construction.Weighted.ExpansionFloors.lowerBoundConst_pos <;> assumption
theorem expansionDecayRate_pos (hL : Conventions.IsAdmissibleBlockingFactor L) :
    0 < Weighted.expansionDecayRate 4 L := by
  have hε := greenDecayRate_pos hL
  have hu := upperBoundConst_pos hL
  have hγ := lowerBoundConst_pos
  have hs := latticeSumConst_pos hL (κ := 1 / 4 * Weighted.greenDecayRate 4 L) (by positivity)
  have hκ : 0 < Weighted.inverseExpansionRate 4 L := by
    unfold Weighted.inverseExpansionRate
    refine lt_min (by positivity) ?_
    positivity
  unfold Weighted.expansionDecayRate
  positivity
theorem compressedGreenLowerBound_pos :
    0 < SeparatedSequences.compressedGreenLowerBound 4 1 := by
  unfold SeparatedSequences.compressedGreenLowerBound SeparatedSequences.testFormEnergyConstant
  positivity
theorem inverseDecayRate_pos (hL : Conventions.IsAdmissibleBlockingFactor L) {δ B : ℝ} (hδ : 0 < δ)
    (hB : 0 < B) : 0 < SeparatedSequences.inverseDecayRate 4 L δ B := by
  have h := cast_pos hL
  have hγ := compressedGreenLowerBound_pos
  have hZ : 0 < SeparatedSequences.compressedEntryConstant 4 L δ B := by
    unfold SeparatedSequences.compressedEntryConstant SeparatedSequences.greenColumnConstant
    positivity
  have hc : 0 < SeparatedSequences.expSumConstant 4 L (δ / 2) := by
    unfold SeparatedSequences.expSumConstant
    positivity
  unfold SeparatedSequences.inverseDecayRate
  refine lt_min (by positivity) ?_
  positivity
end YangMills.Construction.SeparatedClasses.OperatorConstantsPos
end
