import YangMills.Construction.ColdStepAtMirrorFrames.EnergyOfTheShiftOfAChain
import YangMills.Construction.ColdStepAtMirrorFrames.SitesCellsAndPositions
import YangMills.Construction.ColdStepAtMirrorFrames.SquareSumOfTheCurlOfAFlatChain
import YangMills.Construction.ColdStepAtMirrorFrames.WeightsOfPositionsAtACell
import Mathlib
set_option autoImplicit false
noncomputable section
open YangMills.Construction.BlockAverages
namespace YangMills.Construction.ColdStepAtMirrorFrames
variable {F : BlockFrame}
theorem enclosingCell_mem_cellBall_of_nearWeight_ne_zero (hL : Odd F.blockSide) (hs : ∀ i, 0 < F.extent i)
    (h4 : 4 ≤ F.blockSide) (Y : F.Cell) {r : ℝ} (hr : r ≤ 4)
    {j : ℕ} (x : F.Site j) (h : nearWeight (sitePosition Y) r j x ≠ 0) : enclosingCell x ∈ cellBall Y 24 := by
  have hLr : (4 : ℝ) ≤ F.blockSide := by exact_mod_cast h4
  have hLp : (0 : ℝ) < F.blockSide := by linarith
  have hc : j ≤ F.depth ∧ distFromPoint (sitePosition Y) x ≤ r + readReach F j := by
    by_contra hn
    apply h
    unfold nearWeight
    rw [if_neg hn]
  have hj : j ≤ F.top := by
    unfold BlockFrame.top
    omega
  have h1 := readReach_le (F := F) h4 j
  have h2 : 4 / (F.blockSide : ℝ) ≤ 1 := by
    rw [div_le_one hLp]
    exact hLr
  have h3 := distFromPoint_enclosingCell_le hL hs hj x (sitePosition Y)
  exact show cellSupDist (enclosingCell x) Y ≤ 24 from by
    refine siteSupDist_le_of_distFromPoint hL hs le_rfl (enclosingCell x) Y 24 ?_
    simp only [Nat.sub_self, pow_zero, mul_one]
    push_cast
    linarith [hc.2]
open Classical in
theorem sum_sq_mul_le_sum_filter_enclosingCell {j : ℕ} (hj : True) (u : F.Site j → ℝ) (X : Set F.Cell)
    (hu : ∀ x, u x ≠ 0 → enclosingCell x ∈ X) (h01 : ∀ x, u x ^ 2 ≤ 1) (g : F.Site j → ℝ)
    (hg : ∀ x, 0 ≤ g x) :
    ∑ x ∈ allSites F j, u x ^ 2 * g x ≤
      ∑ x ∈ (allSites F j).filter (fun x => enclosingCell x ∈ X), g x := by
  rw [Finset.sum_filter]
  refine Finset.sum_le_sum fun x _ => ?_
  by_cases h : enclosingCell x ∈ X
  · rw [if_pos h]
    have := mul_le_mul_of_nonneg_right (h01 x) (hg x)
    simpa using this
  · rw [if_neg h]
    have : u x = 0 := by
      by_contra hn
      exact h (hu x hn)
    rw [this]
    simp
theorem sq_nearWeight_le_one (c : Fin 4 → ℝ) (r : ℝ) {j : ℕ} (x : F.Site j) :
    nearWeight c r j x ^ 2 ≤ 1 := by
  unfold nearWeight
  split_ifs <;> norm_num
open Classical in
theorem curlSquareSumBound_holds : CurlSquareSumBound := by
  intro a ha
  refine ⟨432, by norm_num, 8, ?_⟩
  intro F c B hL hL8 hcub hB Y
  have hs := extent_pos_of_isLargeCubicTorus hcub
  have hL4 : 4 ≤ F.blockSide := by omega
  have h3 : 3 ≤ F.blockSide := by omega
  have hLr : (8 : ℝ) ≤ F.blockSide := by exact_mod_cast hL8
  have hLp : (0 : ℝ) < F.blockSide := by linarith
  have htn : F.depth ≤ F.top := by
    unfold BlockFrame.top
    omega
  set cp := sitePosition Y with hcp
  set U := nearWeight (F := F) cp 3 with hU
  set V := nearWeight (F := F) cp 4 with hV
  have hUm : IsReadMonotone U := isReadMonotone_nearWeight hL hs hL4 cp 3
  have hVm : IsReadMonotone V := isReadMonotone_nearWeight hL hs hL4 cp 4
  have hcore : ∑ p ∈ (sitesOfCells (finiteCells F) F.depth).filter
      (fun p => cellSupDist (enclosingCell p) Y ≤ 2), ∑ e ∈ orientedPlanes,
      plaquetteCurl (B F.depth) p e.1 e.2 ^ 2 ≤ weightedCurlNormSq (U F.depth) (B F.depth) := by
    unfold weightedCurlNormSq
    calc _ = ∑ p ∈ (allSites F F.depth).filter (fun p => cellSupDist (enclosingCell p) Y ≤ 2),
          ∑ e ∈ orientedPlanes, (U F.depth p * plaquetteCurl (B F.depth) p e.1 e.2) ^ 2 := by
          refine Finset.sum_congr rfl fun p hp => ?_
          have hp2 := (Finset.mem_filter.1 hp).2
          have hu : U F.depth p = 1 := by
            simp only [hU]
            unfold nearWeight
            rw [if_pos]
            refine ⟨le_rfl, ?_⟩
            have a1 := distFromPoint_le_enclosingCell hL hs htn p cp
            have a2 := distFromPoint_le_add_siteSupDist hL hs (enclosingCell p) Y cp
            have a3 : distFromPoint cp Y = 0 := distFromPoint_sitePosition_self Y
            have a4 : (siteSupDist (enclosingCell p) Y : ℝ) ≤ 2 := by exact_mod_cast hp2
            have a5 := readReach_nonneg (F := F) hL4 F.depth
            simp only [Nat.sub_self, pow_zero, div_one] at a2
            linarith
          simp only [hu, one_mul]
      _ ≤ _ := by
          refine Finset.sum_le_sum_of_subset_of_nonneg (Finset.filter_subset _ _) ?_
          intro _ _ _
          exact Finset.sum_nonneg fun _ _ => sq_nonneg _
  have hsplit : weightedCurlNormSq (U F.depth) (B F.depth) ≤
      2 * weightedCurlNormSq (U F.depth) (iteratedLineAverage (B 0) F.depth) +
        2 * weightedCurlNormSq (U F.depth) (chainDefect B F.depth) := by
    unfold weightedCurlNormSq
    rw [Finset.mul_sum, Finset.mul_sum, ← Finset.sum_add_distrib]
    refine Finset.sum_le_sum fun x _ => ?_
    rw [Finset.mul_sum, Finset.mul_sum, ← Finset.sum_add_distrib]
    refine Finset.sum_le_sum fun e _ => ?_
    have e1 : plaquetteCurl (chainDefect B F.depth) x e.1 e.2 =
        plaquetteCurl (iteratedLineAverage (B 0) F.depth) x e.1 e.2 - plaquetteCurl (B F.depth) x e.1 e.2 := by
      unfold chainDefect
      exact plaquetteCurl_sub _ _ _ _ _
    rw [e1]
    set p := plaquetteCurl (iteratedLineAverage (B 0) F.depth) x e.1 e.2
    set q := plaquetteCurl (B F.depth) x e.1 e.2
    set u := U F.depth x
    nlinarith [sq_nonneg (u * p + u * (p - q))]
  have havg := weightedCurlNormSq_iteratedLineAverage_le hL hs hUm (B 0) htn
  have hdefect : weightedCurlNormSq (U F.depth) (chainDefect B F.depth) ≤
      96 * weightedNormSq (V F.depth) (chainDefect B F.depth) := by
    refine weightedCurlNormSq_le_weightedNormSq hL hs htn _ _
      (fun x => sq_nearWeight_le_of_le cp (by norm_num) x) (fun x k => ?_) _
    have h5 := sq_nearWeight_le_of_near cp x (x + unitStep F.depth k) (by
      have hM : (F.blockSide : ℝ) ^ (F.top - F.depth) = F.blockSide := by
        have : F.top - F.depth = 1 := by
          unfold BlockFrame.top
          omega
        rw [this, pow_one]
      have hd := abs_distFromPoint_axisOffset_sub_le hL hs x k 1 cp 1 zero_le_one (by
        rw [hM]
        simp only [Int.cast_one, abs_one]
        rw [div_le_one hLp]
        linarith)
      rwa [axisOffset_one] at hd) 3 4 (by norm_num)
    exact h5
  have hmisfit : weightedNormSq (V F.depth) (chainDefect B F.depth) ≤ 9 / 4 * totalMisfit V B := by
    have g := weightedNorm_chainDefect_le hL hs h3 hVm B htn
    have g2 := pow_le_pow_left₀ (weightedNorm_nonneg _ _) g 2
    rw [weightedNorm_sq, mul_pow, Real.sq_sqrt (totalMisfit_nonneg _ _)] at g2
    refine g2.trans (le_of_eq ?_)
    norm_num
  set X := cellBall Y 24 with hX
  have hbottom : weightedCurlNormSq (U 0) (B 0) ≤
      ∑ x ∈ (sitesOfCells (finiteCells F) 0).filter (fun x => enclosingCell x ∈ X),
        ∑ e ∈ orientedPlanes, plaquetteCurl (B 0) x e.1 e.2 ^ 2 := by
    have := sum_sq_mul_le_sum_filter_enclosingCell (j := 0) trivial (U 0) X
      (fun x hx => enclosingCell_mem_cellBall_of_nearWeight_ne_zero hL hs hL4 Y (by norm_num) x hx)
      (fun x => sq_nearWeight_le_one _ _ x) (fun x => ∑ e ∈ orientedPlanes, plaquetteCurl (B 0) x e.1 e.2 ^ 2)
      (fun x => Finset.sum_nonneg fun _ _ => sq_nonneg _)
    refine le_trans (le_of_eq ?_) this
    unfold weightedCurlNormSq
    refine Finset.sum_congr rfl fun x _ => ?_
    rw [Finset.mul_sum]
    refine Finset.sum_congr rfl fun e _ => ?_
    ring
  have hlevels : totalMisfit V B ≤ ∑ j ∈ Finset.range F.top,
      ∑ y ∈ (sitesOfCells (finiteCells F) (j + 1)).filter (fun y => enclosingCell y ∈ X),
        ∑ i : Fin 4, chainMisfit B j y i ^ 2 := by
    refine Finset.sum_le_sum fun j _ => ?_
    have := sum_sq_mul_le_sum_filter_enclosingCell (j := j + 1) trivial (V (j + 1)) X
      (fun x hx => enclosingCell_mem_cellBall_of_nearWeight_ne_zero hL hs hL4 Y le_rfl x hx)
      (fun x => sq_nearWeight_le_one _ _ x) (fun y => ∑ i : Fin 4, chainMisfit B j y i ^ 2)
      (fun x => Finset.sum_nonneg fun _ _ => sq_nonneg _)
    refine le_trans (le_of_eq ?_) this
    unfold weightedNormSq
    refine Finset.sum_congr rfl fun x _ => ?_
    rw [Finset.mul_sum]
    refine Finset.sum_congr rfl fun e _ => ?_
    ring
  set c0 := ∑ x ∈ (sitesOfCells (finiteCells F) 0).filter (fun x => enclosingCell x ∈ X),
      ∑ e ∈ orientedPlanes, plaquetteCurl (B 0) x e.1 e.2 ^ 2 with hc0
  set c1 := ∑ j ∈ Finset.range F.top,
      ∑ y ∈ (sitesOfCells (finiteCells F) (j + 1)).filter (fun y => enclosingCell y ∈ X),
        ∑ i : Fin 4, chainMisfit B j y i ^ 2 with hc1
  have hen : chainEnergyOnCells a B X = c0 + a * c1 := rfl
  have hc0n : 0 ≤ c0 := Finset.sum_nonneg fun _ _ => Finset.sum_nonneg fun _ _ => sq_nonneg _
  have hc1n : 0 ≤ c1 := Finset.sum_nonneg fun _ _ => Finset.sum_nonneg fun _ _ =>
    Finset.sum_nonneg fun _ _ => sq_nonneg _
  rw [hen]
  nlinarith
end YangMills.Construction.ColdStepAtMirrorFrames
end
