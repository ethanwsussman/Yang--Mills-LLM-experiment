import YangMills.Construction.Torus.BoundsOnTheAveragedSquareProof
import Mathlib
set_option autoImplicit false
noncomputable section
namespace YangMills.Construction.Weighted.ExpansionFloors
theorem greenDecayRate_pos {L : ℕ} (hL : 3 ≤ L) : 0 < greenDecayRate 4 L := by apply _root_.YangMills.Construction.Weighted.AvgGreenSqBounds.greenDecayRate_pos <;> assumption
theorem latticeSumConst_pos {L : ℕ} (hL : 3 ≤ L) {κ : ℝ} (hκ : 0 < κ) :
    0 < latticeSumConst 4 L κ := by
  unfold latticeSumConst
  positivity
theorem coercivityConst_pos {L : ℕ} (hL : 3 ≤ L) : 0 < coercivityConst L := by
  have hthree : (3 : ℝ) ≤ L := by exact_mod_cast hL
  have hsq : (1 : ℝ) < (L : ℝ) ^ 2 := by nlinarith
  unfold coercivityConst
  have := inv_lt_one_of_one_lt₀ hsq
  linarith
theorem weightedBoundConst_pos {L : ℕ} (hL : 3 ≤ L) : 0 < weightedBoundConst 4 L := by
  have hc := coercivityConst_pos hL
  have he := greenDecayRate_pos hL
  unfold weightedBoundConst
  have h1 : 0 < 4 / coercivityConst L := by positivity
  have h2 : 0 ≤ Real.sqrt (8 / coercivityConst L) := Real.sqrt_nonneg _
  have h3 : 0 ≤ 8 * greenDecayRate 4 L * (L : ℝ) * Real.sqrt ((4 : ℕ) : ℝ) / coercivityConst L := by
    positivity
  exact mul_pos (Real.exp_pos _) (by linarith)
theorem upperBoundConst_pos {L : ℕ} (hL : 3 ≤ L) : 0 < upperBoundConst 4 L := by
  have hw := weightedBoundConst_pos hL
  have hs := latticeSumConst_pos hL (κ := 1 / 4 * greenDecayRate 4 L)
    (by have := greenDecayRate_pos hL; positivity)
  unfold upperBoundConst
  positivity
theorem lowerBoundConst_pos : 0 < lowerBoundConst 4 := by
  have hbase : 0 < lowerBoundBaseConst 4 := by
    unfold lowerBoundBaseConst testLaplacianConst
    have := Real.pi_pos
    positivity
  unfold lowerBoundConst
  positivity
theorem inverseExpansionRate_pos {L : ℕ} (hL : 3 ≤ L) : 0 < inverseExpansionRate 4 L := by
  have he := greenDecayRate_pos hL
  have hC := upperBoundConst_pos hL
  have hg := lowerBoundConst_pos
  have hs := latticeSumConst_pos hL (κ := 1 / 4 * greenDecayRate 4 L) (by positivity)
  unfold inverseExpansionRate
  exact lt_min (by positivity) (by positivity)
theorem expansionDecayRate_pos {L : ℕ} (hL : 3 ≤ L) : 0 < expansionDecayRate 4 L := by
  have he := greenDecayRate_pos hL
  have hk := inverseExpansionRate_pos hL
  unfold expansionDecayRate
  have : 0 < min (inverseExpansionRate 4 L) (1 / 16 * greenDecayRate 4 L) :=
    lt_min hk (by positivity)
  positivity
theorem two_mul_expansionDecayRate_le (L : ℕ) :
    2 * expansionDecayRate 4 L ≤ inverseExpansionRate 4 L := by
  have := min_le_left (inverseExpansionRate 4 L) (1 / 16 * greenDecayRate 4 L)
  unfold expansionDecayRate
  linarith
theorem expansionDecayRate_le_greenDecayRate (L : ℕ) :
    expansionDecayRate 4 L ≤ 1 / 32 * greenDecayRate 4 L := by
  have := min_le_right (inverseExpansionRate 4 L) (1 / 16 * greenDecayRate 4 L)
  unfold expansionDecayRate
  linarith
theorem inverseExpansionRate_eq_decayRateOfInverse (L : ℕ) :
    inverseExpansionRate 4 L =
      decayRateOfInverse L (lowerBoundConst 4) (1 / 2 * greenDecayRate 4 L) (upperBoundConst 4 L) := by
  have halve : ∀ a e C S : ℝ, a * e / (16 * C * S) = a * (1 / 2 * e) / (8 * C * S) := by
    intro a e C S
    rw [show a * (1 / 2 * e) = a * e / 2 by ring, div_div]
    congr 1
    ring
  unfold inverseExpansionRate decayRateOfInverse
  rw [show 1 / 2 * greenDecayRate 4 L / 2 = 1 / 4 * greenDecayRate 4 L by ring,
    show 1 / 2 * greenDecayRate 4 L / 4 = greenDecayRate 4 L / 8 by ring]
  congr 1
  have := halve (Real.exp 1 * lowerBoundConst 4) (greenDecayRate 4 L) (upperBoundConst 4 L)
    (latticeSumConst 4 L (1 / 4 * greenDecayRate 4 L))
  simpa only [mul_assoc] using this
theorem constantsOrder_of_factor {L : ℕ} (hL : Blocking.FourDimOddFactor 4 L) :
    ConstantsOrder L := by
  have h3 := hL.three_le_factor
  refine ⟨by have := expansionDecayRate_pos h3; positivity, two_mul_expansionDecayRate_le L,
    expansionDecayRate_le_greenDecayRate L, fun c _ => ?_, inverseExpansionRate_eq_decayRateOfInverse L⟩
  unfold expansionBlockSizeFloor
  exact le_max_left _ _
theorem floorConsequences_of_le (D : TorusData)
    (hD : expansionSeparationFloor 4 D.L ≤ (D.gapNumber : ℝ) * (D.blockNumber : ℝ)) :
    FloorConsequences D := by
  have h3 := D.blocking.three_le_factor
  have hδ := expansionDecayRate_pos h3
  have hε := greenDecayRate_pos h3
  have hle := expansionDecayRate_le_greenDecayRate D.L
  have ha : 0 ≤ Real.log (D.L : ℝ) :=
    Real.log_nonneg (by exact_mod_cast (by omega : 1 ≤ D.L))
  unfold FloorConsequences TorusData.scaleRatioRate latticeSumRadius
  unfold expansionSeparationFloor at hD
  generalize (D.gapNumber : ℝ) * (D.blockNumber : ℝ) = X at hD ⊢
  generalize Real.log (D.L : ℝ) = a at ha hD ⊢
  rw [show 4 * (((4 : ℕ) : ℝ) + 2) * (a + 1) = 24 * (a + 1) by push_cast; ring] at hD
  have hX : 0 < X := lt_of_lt_of_le (div_pos (by linarith) hδ) hD
  have hfl : 24 * (a + 1) ≤ X * expansionDecayRate 4 D.L := (div_le_iff₀ hδ).mp hD
  have hXε : X * (32 * expansionDecayRate 4 D.L) ≤ X * greenDecayRate 4 D.L :=
    mul_le_mul_of_nonneg_left (by linarith) hX.le
  refine ⟨?_, ?_, ?_, fun κ hκ => ?_, ?_, by linarith⟩
  · rw [div_le_iff₀ hε]
    nlinarith
  · rw [div_le_iff₀ hε]
    nlinarith
  · rw [div_le_iff₀ (mul_pos (by norm_num) hε)]
    nlinarith
  · have hκ0 : 0 < κ := by linarith
    have hXκ : X * (1 / 2 * expansionDecayRate 4 D.L) ≤ X * κ :=
      mul_le_mul_of_nonneg_left hκ hX.le
    rw [div_le_iff₀ hκ0]
    push_cast
    nlinarith
  · have : a / X ≤ 1 / 8 * expansionDecayRate 4 D.L := by
      rw [div_le_iff₀ hX]
      nlinarith
    linarith
theorem statement_holds : Statement :=
  ⟨⟨⟨fun p => (inverseExpansionRate p.1 p.2, expansionDecayRate p.1 p.2,
        expansionSeparationFloor p.1 p.2),
      fun _ => rfl⟩,
    ⟨fun q => (expansionConstFirst q.1 q.2.1 q.2.2, expansionConstSecond q.1 q.2.1 q.2.2,
        expansionBlockSizeFloor q.1 q.2.1 q.2.2, expansionConstBound q.1 q.2.1 q.2.2),
      fun _ => rfl⟩⟩,
    fun _ hL => constantsOrder_of_factor hL, floorConsequences_of_le⟩
end YangMills.Construction.Weighted.ExpansionFloors
end
