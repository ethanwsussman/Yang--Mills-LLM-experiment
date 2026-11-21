import YangMills.Construction.BoundsOnEverySide.MovingTuplesOfALimitAlongStatesProof
import YangMills.Construction.SystemsWithFiveBounds.ConditionsAtFixedConstants
import YangMills.Construction.SystemsWithFiveBounds.GrowthOfALimitAtNumbers
import YangMills.Construction.SystemsWithFiveBounds.RotationsAtTheChosenConstants
import Mathlib
set_option autoImplicit false
noncomputable section
namespace YangMills.Construction
namespace TestFunctions
private theorem sharpNormR4_nonneg (M : ℝ) (f : (Fin 4 → ℝ) → ℝ) : 0 ≤ sharpNormR4 M f := by apply _root_.YangMills.Construction.BoundsOnEverySide.TranslatedTuples.sharpNormR4_nonneg <;> assumption
end TestFunctions
namespace SystemsWithFiveBounds.BoundConstants
variable (N : BoundConstants)
private theorem one_le_separationWeightAt (d : ℝ) : 1 ≤ N.separationWeightAt d := le_max_left _ _
private theorem separationWeightAt_antitone {d d' : ℝ} (hd : 0 < d) (h : d ≤ d') :
    N.separationWeightAt d' ≤ N.separationWeightAt d := by
  refine max_le_max le_rfl ?_
  rw [zpow_neg, zpow_neg, zpow_natCast, zpow_natCast]
  exact inv_anti₀ (pow_pos hd _) (pow_le_pow_left₀ hd.le h _)
private theorem cumulantBound_eq_product (n : ℕ) (d R : ℝ) :
    N.cumulantBound n d R =
      (N.aStar * N.separationWeightAt d * N.ballConst R) ^ n * (n.factorial : ℝ) ^ N.factorialExponent := rfl
variable {N}
private theorem cumulantBound_pos_of_admissible (h : N.Admissible) (n : ℕ) (d : ℝ) {R : ℝ} (hR : 0 < R) :
    0 < N.cumulantBound n d R := by
  have h₁ := h.aStar_pos
  have h₂ := h.ballConst_pos R hR
  have h₃ : 0 < N.separationWeightAt d := lt_of_lt_of_le one_pos (N.one_le_separationWeightAt d)
  rw [cumulantBound_eq_product]
  have : (0 : ℝ) < (n.factorial : ℝ) := by exact_mod_cast n.factorial_pos
  positivity
abbrev _root_.YangMills.SharedProofs.p39650 := @cumulantBound_pos_of_admissible
private theorem cumulantBound_antitone_of_admissible (h : N.Admissible) (n : ℕ) {d d' R : ℝ} (hd : 0 < d)
    (hle : d ≤ d') (hR : 0 < R) : N.cumulantBound n d' R ≤ N.cumulantBound n d R := by
  have h₁ := h.aStar_pos
  have h₂ := h.ballConst_pos R hR
  have h₃ : 0 < N.separationWeightAt d' := lt_of_lt_of_le one_pos (N.one_le_separationWeightAt d')
  rw [cumulantBound_eq_product, cumulantBound_eq_product]
  refine mul_le_mul_of_nonneg_right (pow_le_pow_left₀ (by positivity) ?_ n) (by positivity)
  exact mul_le_mul_of_nonneg_right
    (mul_le_mul_of_nonneg_left (N.separationWeightAt_antitone hd hle) h₁.le) h₂.le
abbrev _root_.YangMills.SharedProofs.p25134 := @cumulantBound_antitone_of_admissible
end SystemsWithFiveBounds.BoundConstants
namespace WindowLimits
private theorem enclosingSideOf_pos (X Y : SeparatedTuples.SepTuple) : 0 < (enclosingSideOf X Y : ℝ) := by
  unfold enclosingSideOf
  positivity
private theorem clusteringRadiusOf_pos (X Y : SeparatedTuples.SepTuple) : 0 < clusteringRadiusOf X Y := by
  unfold clusteringRadiusOf
  have := enclosingSideOf_pos X Y
  positivity
end WindowLimits
namespace SystemsWithFiveBounds
private theorem clusteringConstOf_pos (M : ℝ) (N : BoundConstants) (X Y : SeparatedTuples.SepTuple) :
    0 < clusteringConstOf M N X Y := by
  unfold clusteringConstOf
  positivity
private theorem existentialConstants_sideConditions {M : ℝ} {N : BoundConstants} (hM : 1 ≤ M)
    (hN : N.Admissible) : (existentialConstants M N).SideConditions := by
  have hC : 0 < powerConst N := mul_pos hN.aStar_pos (hN.ballConst_pos 1 one_pos)
  have hb : (1 : ℝ) ≤ SeparatedBound.extBaseMax := le_max_left _ _
  have hB : 0 < SeparatedPowerBound.powerBase M N.sepExponent (powerConst N) := by
    have hM' : 0 < M := by linarith
    have hb' : 0 < SeparatedBound.extBaseMax := by linarith
    unfold SeparatedPowerBound.powerBase
    positivity
  have hu : 0 ≤ unitBallBound M N :=
    mul_nonneg (hN.onePointConst_nonneg 1 one_pos) (Real.sInf_nonneg (by
      rintro _ ⟨f, -, rfl⟩
      exact TestFunctions.sharpNormR4_nonneg _ _))
  have hf : 0 ≤ SeparatedBound.extFactorAbs := abs_nonneg _
  refine ⟨?_, fun n _ R hR d hd d' _ hle => ?_, fun n _ d R _ hR => ?_, fun d R _ _ => ?_,
    fun R hR => ?_, ?_, ?_, ?_, ?_, fun X Y => clusteringConstOf_pos M N X Y,
    WindowLimits.clusteringRadiusOf_pos⟩
  · exact add_nonneg hN.factorialExponent_nonneg zero_le_one
  · exact BoundConstants.cumulantBound_antitone_of_admissible hN n hd hle hR
  · exact BoundConstants.cumulantBound_pos_of_admissible hN n d hR
  · exact Real.exp_pos _
  · exact hN.ballConst_pos R hR
  · show 0 < 10 + N.sepExponent
    omega
  · show 0 < 1 + 2 * SeparatedBound.extFactorAbs
    linarith
  · show 0 < TestSpaces.onePointConst _ _ _
    unfold TestSpaces.onePointConst
    have := mul_nonneg hu
      (ENNReal.toReal_nonneg (a := TestSpaces.weightIntegral (10 + N.sepExponent)))
    linarith
  · show 0 < 20 + N.factorialExponent
    linarith [hN.factorialExponent_nonneg]
theorem limitConditionsExist_of_inputs (hC : BaseAndLawConditionsAtExistentialConstants)
    (hR : RotationConditionsAtExistentialConstants) : LimitConditionsExist := fun M N hM hN =>
  ⟨existentialConstants M N, existentialConstants_sideConditions hM hN, (hC M N).1, (hC M N).2,
    hR M N (existentialConstants_sideConditions hM hN)⟩
end SystemsWithFiveBounds
end YangMills.Construction
