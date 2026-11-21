import YangMills.Construction.ColdChainAtEveryLevel.CompositeMeanOfTheGeneratorsProof
import YangMills.Construction.ColdChainAtEveryLevel.GapsOfTheLevelsNearACell
import Mathlib
set_option autoImplicit false
noncomputable section
open scoped Quaternion
namespace YangMills.Construction.BlockAverages
namespace LevelCoordinates
variable {F : BlockFrame}
theorem cellSupDist_le_of_mem_cellBall {S : Finset F.Cell} {z y : F.Cell} {r : ℕ} (h : y ∈ cellBall S z r) :
    cellSupDist z y ≤ r := by
  classical
  unfold cellBall at h
  exact (Finset.mem_filter.1 h).2
theorem localNorm_nonneg (S : Finset F.Cell) (R : F.FieldChain) (U : ChainChart F) (w : F.SiteWeights)
    (z : F.Cell) : 0 ≤ localNorm S R U w z := Real.sqrt_nonneg _
theorem localNorm_constOne_le_supWeightedNorm (S : Finset F.Cell) (R : F.FieldChain) (U : ChainChart F)
    {del : ℝ} (hdel : 0 < del) {z : F.Cell} (hz : z ∈ S) :
    localNorm S R U (constOneWeights F) z ≤ Real.exp (3 * del) * supWeightedNorm S del R U := by apply _root_.YangMills.Construction.BlockAverages.GeneratorMeans.localNorm_le_supWeightedNorm <;> assumption
theorem sqrt_sqrt_le_of_le_pow_four {x y : ℝ} (hy : 0 ≤ y) (h : x ≤ y ^ 4) : Real.sqrt (Real.sqrt x) ≤ y := by
  calc Real.sqrt (Real.sqrt x) ≤ Real.sqrt (Real.sqrt (y ^ 4)) := Real.sqrt_le_sqrt (Real.sqrt_le_sqrt h)
    _ = y := by
      rw [show y ^ 4 = (y ^ 2) ^ 2 by ring, Real.sqrt_sq (by positivity), Real.sqrt_sq hy]
end LevelCoordinates
open LevelCoordinates in
theorem levelCoordinateQuarticStatement_of_levelGapNearCellStatement (hG : levelGapNearCellStatement) :
    levelCoordinateQuarticStatement := by
  obtain ⟨C, hC, L₀, hL⟩ := hG
  refine ⟨2 * C, L₀, by positivity, fun L hodd hL0 del hdel => ?_⟩
  obtain ⟨c, hc, h⟩ := hL L hodd hL0
  refine ⟨c * Real.exp (-(3 * del)), by positivity, ?_⟩
  intro F m S hFL hamb hm hreg s V hs hsc hcold U hU j hj z hz
  have hcle : c * Real.exp (-(3 * del)) ≤ c :=
    mul_le_of_le_one_right hc.le (Real.exp_le_one_iff.2 (by linarith))
  have hβ0 : 0 ≤ localNorm S (referenceFieldChain S V) U (constOneWeights F) z := localNorm_nonneg _ _ _ _ _
  have hβ : localNorm S (referenceFieldChain S V) U (constOneWeights F) z ≤ c := by
    refine (localNorm_constOne_le_supWeightedNorm S _ U hdel hz).trans ?_
    calc Real.exp (3 * del) * supWeightedNorm S del (referenceFieldChain S V) U
        ≤ Real.exp (3 * del) * (c * Real.exp (-(3 * del))) :=
          mul_le_mul_of_nonneg_left hU (Real.exp_pos _).le
      _ = c := by
        rw [mul_left_comm, ← Real.exp_add]
        simp
  have hgap := (h F m S hFL hamb hm hreg s V hs (hsc.trans hcle) hcold U z _ hz hβ0 hβ (le_of_eq rfl) j hj).2
  refine sqrt_sqrt_le_of_le_pow_four (by positivity) ?_
  calc ∑ b ∈ bondsOver S {z} j, ‖levelCoordinate (referenceFieldChain S V) U j b.1 b.2‖ ^ 4
      ≤ ∑ b ∈ bondsOver S {z} j,
          2 ^ 4 * normSubOne (chartGap (referenceFieldChain S V) U j b.1 b.2) ^ 4 := by
        refine Finset.sum_le_sum fun b _ => ?_
        rw [← mul_pow]
        exact pow_le_pow_left₀ (norm_nonneg _) (norm_unitQuaternionLog_le_two_mul _) 4
    _ = 2 ^ 4 * ∑ b ∈ bondsOver S {z} j,
          normSubOne (chartGap (referenceFieldChain S V) U j b.1 b.2) ^ 4 := by
        rw [Finset.mul_sum]
    _ ≤ 2 ^ 4 * (C * localNorm S (referenceFieldChain S V) U (constOneWeights F) z) ^ 4 :=
        mul_le_mul_of_nonneg_left hgap (by norm_num)
    _ = _ := by ring
end YangMills.Construction.BlockAverages
end
