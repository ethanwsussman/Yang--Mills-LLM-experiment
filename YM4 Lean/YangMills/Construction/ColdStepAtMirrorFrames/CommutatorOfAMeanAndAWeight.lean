import YangMills.Construction.ColdStepAtMirrorFrames.TestChainOfAFlatChain
import Mathlib
set_option autoImplicit false
noncomputable section
open YangMills.Construction.BlockAverages
namespace YangMills.Construction.ColdStepAtMirrorFrames
variable {F : BlockFrame}
theorem sum_sq_lineKernel_le (hL : Odd F.blockSide) (hs : ∀ i, 0 < F.extent i) {j : ℕ} (hj : j + 1 ≤ F.top)
    (i : Fin 4) (u : F.Site (j + 1) → ℝ) (v : F.Site j → ℝ) (κ : ℝ) (hκ : 0 ≤ κ) (g : F.Site j → ℝ)
    (m : F.Site (j + 1) → (Fin 4 → ℤ) → ℕ → ℝ)
    (hw : ∀ y, ∀ h ∈ centredCube F.blockSide, ∀ l ∈ Finset.range F.blockSide,
      u y ^ 2 * m y h l ^ 2 ≤
        κ * v (BlockAverages.refineSite y + siteOfCoords j h + axisOffset j i (l : ℤ)) ^ 2) :
    ∑ y ∈ allSites F (j + 1), (u y * ((1 / (F.blockSide : ℝ) ^ 4) * ∑ h ∈ centredCube F.blockSide,
        ∑ l ∈ Finset.range F.blockSide,
        m y h l * g (BlockAverages.refineSite y + siteOfCoords j h + axisOffset j i (l : ℤ)))) ^ 2 ≤
      κ / (F.blockSide : ℝ) ^ 2 * ∑ x ∈ allSites F j, (v x * g x) ^ 2 := by
  obtain ⟨k, hk⟩ := id hL
  have hLr : (0 : ℝ) < F.blockSide := by
    have : 0 < F.blockSide := by omega
    exact_mod_cast this
  have hb0 : (F.blockSide : ℝ) ≠ 0 := hLr.ne'
  have hc : ((centredCube F.blockSide).card : ℝ) = (F.blockSide : ℝ) ^ 4 := by
    rw [card_centredCube hk]
    push_cast
    rfl
  have key : (1 : ℝ) / (F.blockSide : ℝ) ^ 8 * ((F.blockSide : ℝ) ^ 4 * F.blockSide) =
      1 / (F.blockSide : ℝ) ^ 3 := by
    field_simp
  have hy : ∀ y, (u y * ((1 / (F.blockSide : ℝ) ^ 4) * ∑ h ∈ centredCube F.blockSide,
        ∑ l ∈ Finset.range F.blockSide,
        m y h l * g (BlockAverages.refineSite y + siteOfCoords j h + axisOffset j i (l : ℤ)))) ^ 2 ≤
      κ / (F.blockSide : ℝ) ^ 3 * ∑ h ∈ centredCube F.blockSide, ∑ l ∈ Finset.range F.blockSide,
        (v (BlockAverages.refineSite y + siteOfCoords j h + axisOffset j i (l : ℤ)) *
          g (BlockAverages.refineSite y + siteOfCoords j h + axisOffset j i (l : ℤ))) ^ 2 := by
    intro y
    have c1 := sq_sum_sum_le_card_mul (centredCube F.blockSide) (Finset.range F.blockSide)
      (fun h l => m y h l * g (BlockAverages.refineSite y + siteOfCoords j h + axisOffset j i (l : ℤ)))
    rw [hc, Finset.card_range] at c1
    have c2 : u y ^ 2 * ∑ h ∈ centredCube F.blockSide, ∑ l ∈ Finset.range F.blockSide,
          (m y h l * g (BlockAverages.refineSite y + siteOfCoords j h + axisOffset j i (l : ℤ))) ^ 2 ≤
        κ * ∑ h ∈ centredCube F.blockSide, ∑ l ∈ Finset.range F.blockSide,
        (v (BlockAverages.refineSite y + siteOfCoords j h + axisOffset j i (l : ℤ)) *
          g (BlockAverages.refineSite y + siteOfCoords j h + axisOffset j i (l : ℤ))) ^ 2 := by
      rw [Finset.mul_sum, Finset.mul_sum]
      refine Finset.sum_le_sum fun h hh => ?_
      rw [Finset.mul_sum, Finset.mul_sum]
      refine Finset.sum_le_sum fun l hl => ?_
      rw [mul_pow, mul_pow, ← mul_assoc, ← mul_assoc]
      exact mul_le_mul_of_nonneg_right (hw y h hh l hl) (sq_nonneg _)
    have hu := sq_nonneg (u y)
    calc _ = u y ^ 2 * (1 / (F.blockSide : ℝ) ^ 8) * (∑ h ∈ centredCube F.blockSide,
          ∑ l ∈ Finset.range F.blockSide,
          m y h l * g (BlockAverages.refineSite y + siteOfCoords j h + axisOffset j i (l : ℤ))) ^ 2 := by
          ring
      _ ≤ u y ^ 2 * (1 / (F.blockSide : ℝ) ^ 8) * (((F.blockSide : ℝ) ^ 4 * (F.blockSide : ℝ)) *
          ∑ h ∈ centredCube F.blockSide, ∑ l ∈ Finset.range F.blockSide,
          (m y h l * g (BlockAverages.refineSite y + siteOfCoords j h + axisOffset j i (l : ℤ))) ^ 2) :=
          mul_le_mul_of_nonneg_left c1 (by positivity)
      _ = (1 / (F.blockSide : ℝ) ^ 3) * (u y ^ 2 * ∑ h ∈ centredCube F.blockSide,
          ∑ l ∈ Finset.range F.blockSide,
          (m y h l * g (BlockAverages.refineSite y + siteOfCoords j h + axisOffset j i (l : ℤ))) ^ 2) := by
          rw [← key]
          ring
      _ ≤ (1 / (F.blockSide : ℝ) ^ 3) * (κ * ∑ h ∈ centredCube F.blockSide, ∑ l ∈ Finset.range F.blockSide,
        (v (BlockAverages.refineSite y + siteOfCoords j h + axisOffset j i (l : ℤ)) *
          g (BlockAverages.refineSite y + siteOfCoords j h + axisOffset j i (l : ℤ))) ^ 2) :=
          mul_le_mul_of_nonneg_left c2 (by positivity)
      _ = _ := by
          ring
  calc _ ≤ ∑ y ∈ allSites F (j + 1), κ / (F.blockSide : ℝ) ^ 3 * ∑ h ∈ centredCube F.blockSide,
        ∑ l ∈ Finset.range F.blockSide,
        (v (BlockAverages.refineSite y + siteOfCoords j h + axisOffset j i (l : ℤ)) *
          g (BlockAverages.refineSite y + siteOfCoords j h + axisOffset j i (l : ℤ))) ^ 2 :=
        Finset.sum_le_sum fun y _ => hy y
    _ = κ / (F.blockSide : ℝ) ^ 3 * ((F.blockSide : ℝ) * ∑ x ∈ allSites F j, (v x * g x) ^ 2) := by
        rw [← Finset.mul_sum, sum_blocks_lines hL hs hj i (fun x => (v x * g x) ^ 2)]
    _ = _ := by
        field_simp
theorem weightCommutator_eq (W : (j : ℕ) → F.Site j → ℝ) (B : FormChain F) (j : ℕ) (y : F.Site (j + 1))
    (i : Fin 4) :
    weightCommutator W B j y i = (1 / (F.blockSide : ℝ) ^ 4) * ∑ h ∈ centredCube F.blockSide,
      ∑ l ∈ Finset.range F.blockSide,
      (W j (BlockAverages.refineSite y + siteOfCoords j h + axisOffset j i (l : ℤ)) - W (j + 1) y) *
        B j (BlockAverages.refineSite y + siteOfCoords j h + axisOffset j i (l : ℤ)) i := by
  have e1 : lineAverage (weightedChain W B j) y i = (1 / (F.blockSide : ℝ) ^ 4) *
      ∑ h ∈ centredCube F.blockSide, ∑ l ∈ Finset.range F.blockSide,
      W j (BlockAverages.refineSite y + siteOfCoords j h + axisOffset j i (l : ℤ)) *
        B j (BlockAverages.refineSite y + siteOfCoords j h + axisOffset j i (l : ℤ)) i := rfl
  have e2 : lineAverage (B j) y i = (1 / (F.blockSide : ℝ) ^ 4) * ∑ h ∈ centredCube F.blockSide,
      ∑ l ∈ Finset.range F.blockSide,
      B j (BlockAverages.refineSite y + siteOfCoords j h + axisOffset j i (l : ℤ)) i := rfl
  unfold weightCommutator
  rw [e1, e2, mul_left_comm, ← mul_sub, Finset.mul_sum, ← Finset.sum_sub_distrib]
  congr 1
  refine Finset.sum_congr rfl fun h _ => ?_
  rw [Finset.mul_sum, ← Finset.sum_sub_distrib]
  refine Finset.sum_congr rfl fun l _ => ?_
  ring
end YangMills.Construction.ColdStepAtMirrorFrames
end
