import YangMills.Construction.ColdStepAtMirrorFrames.ChainsUnderReadWeights
import YangMills.Construction.ColdStepAtMirrorFrames.PositionsOnATorus
import YangMills.Construction.ColdStepAtMirrorFrames.TestChainOfAFlatChain
import Mathlib
set_option autoImplicit false
noncomputable section
namespace YangMills.Construction.ColdStepAtMirrorFrames
variable {F : BlockAverages.BlockFrame}
def distFromPoint (c : Fin 4 → ℝ) {j : ℕ} (x : F.Site j) : ℝ :=
  Finset.univ.sup' Finset.univ_nonempty fun i => distToMultiples (F.extent i) (cellCoordinate x i - c i)
theorem le_distFromPoint (c : Fin 4 → ℝ) {j : ℕ} (x : F.Site j) (i : Fin 4) :
    distToMultiples (F.extent i) (cellCoordinate x i - c i) ≤ distFromPoint c x :=
  Finset.le_sup' (fun i => distToMultiples (F.extent i) (cellCoordinate x i - c i)) (Finset.mem_univ i)
theorem distFromPoint_nonneg (c : Fin 4 → ℝ) {j : ℕ} (x : F.Site j) : 0 ≤ distFromPoint c x :=
  (distToMultiples_nonneg _ _).trans (le_distFromPoint c x 0)
theorem cellCoordinate_siteOfCoords_distToMultiples (hL : Odd F.blockSide) (hs : ∀ i, 0 < F.extent i)
    {j : ℕ} (v : Fin 4 → ℤ) (c : ℝ) (i : Fin 4) :
    distToMultiples (F.extent i) (cellCoordinate (BlockAverages.siteOfCoords j v : F.Site j) i - c) =
      distToMultiples (F.extent i) ((v i : ℝ) / (F.blockSide : ℝ) ^ (F.top - j) - c) := by
  have hM : (0 : ℝ) < (F.blockSide : ℝ) ^ (F.top - j) := by
    have : 0 < F.blockSide := hL.pos
    positivity
  have hside : (F.extent i : ℝ) ≠ 0 := by
    have := hs i
    positivity
  unfold cellCoordinate
  rw [siteCoords_siteOfCoords]
  have e := Int.emod_add_mul_ediv (v i) (F.period j i : ℤ)
  have e' : ((v i % (F.period j i : ℤ) : ℤ) : ℝ) =
      (v i : ℝ) - (F.period j i : ℝ) * ((v i / (F.period j i : ℤ) : ℤ) : ℝ) := by
    have : ((v i % (F.period j i : ℤ) + (F.period j i : ℤ) * (v i / (F.period j i : ℤ)) : ℤ) : ℝ) =
        (v i : ℝ) := by
      rw [e]
    push_cast at this
    linarith
  rw [e']
  have hp : (F.period j i : ℝ) = (F.extent i : ℝ) * (F.blockSide : ℝ) ^ (F.top - j) := by
    rw [period_eq_extent_mul]
    push_cast
    rfl
  rw [hp]
  have e2 : ((v i : ℝ) - (F.extent i : ℝ) * (F.blockSide : ℝ) ^ (F.top - j) *
      ((v i / (F.period j i : ℤ) : ℤ) : ℝ)) / (F.blockSide : ℝ) ^ (F.top - j) - c =
      ((v i : ℝ) / (F.blockSide : ℝ) ^ (F.top - j) - c) +
        (F.extent i : ℝ) * ((- (v i / (F.period j i : ℤ)) : ℤ) : ℝ) := by
    push_cast
    field_simp
    ring
  rw [e2, distToMultiples_add_mul_int hside]
theorem distFromPoint_add_le (hL : Odd F.blockSide) (hs : ∀ i, 0 < F.extent i) {j : ℕ} (x : F.Site j)
    (h : Fin 4 → ℤ) (c : Fin 4 → ℝ) (t : ℝ)
    (ht : ∀ i, |(h i : ℝ)| / (F.blockSide : ℝ) ^ (F.top - j) ≤ t) :
    distFromPoint c (x + BlockAverages.siteOfCoords j h) ≤ distFromPoint c x + t := by
  have hM : (0 : ℝ) < (F.blockSide : ℝ) ^ (F.top - j) := by
    have : 0 < F.blockSide := hL.pos
    positivity
  unfold distFromPoint
  refine Finset.sup'_le _ _ fun i _ => ?_
  have e1 : x + BlockAverages.siteOfCoords j h =
      BlockAverages.siteOfCoords j (BlockAverages.siteCoords x + h) := by
    rw [siteOfCoords_add, siteOfCoords_siteCoords]
  rw [e1, cellCoordinate_siteOfCoords_distToMultiples hL hs]
  have hsi : (0 : ℝ) < F.extent i := by exact_mod_cast hs i
  have e2 : (((BlockAverages.siteCoords x + h) i : ℤ) : ℝ) / (F.blockSide : ℝ) ^ (F.top - j) - c i =
      ((BlockAverages.siteCoords x i : ℝ) / (F.blockSide : ℝ) ^ (F.top - j) - c i) +
        (h i : ℝ) / (F.blockSide : ℝ) ^ (F.top - j) := by
    simp only [Pi.add_apply]
    push_cast
    ring
  rw [e2]
  refine (distToMultiples_add_le hsi _ _).trans ?_
  have e3 : distToMultiples (F.extent i)
      ((BlockAverages.siteCoords x i : ℝ) / (F.blockSide : ℝ) ^ (F.top - j) - c i) ≤
      Finset.univ.sup' Finset.univ_nonempty
        (fun i => distToMultiples (F.extent i) (cellCoordinate x i - c i)) := by
    refine le_trans (le_of_eq ?_) (Finset.le_sup'
      (fun i => distToMultiples (F.extent i) (cellCoordinate x i - c i)) (Finset.mem_univ i))
    rfl
  have e4 : |(h i : ℝ) / (F.blockSide : ℝ) ^ (F.top - j)| ≤ t := by
    rw [abs_div, abs_of_pos hM]
    exact ht i
  linarith
theorem distFromPoint_refineSite (hL : Odd F.blockSide) (hs : ∀ i, 0 < F.extent i) {j l : ℕ}
    (hjl : j ≤ l) (hl : l ≤ F.top) (y : F.Site l) (c : Fin 4 → ℝ) :
    distFromPoint c (refineSite j l y) = distFromPoint c y := by
  have hLp : (0 : ℝ) < F.blockSide := by exact_mod_cast hL.pos
  unfold distFromPoint refineSite
  congr 1
  funext i
  conv_rhs => rw [← siteOfCoords_siteCoords y]
  rw [cellCoordinate_siteOfCoords_distToMultiples hL hs, cellCoordinate_siteOfCoords_distToMultiples hL hs]
  congr 2
  have e : F.top - j = (F.top - l) + (l - j) := by omega
  rw [e, pow_add]
  push_cast
  field_simp
theorem distFromPoint_blockRefine (hL : Odd F.blockSide) (hs : ∀ i, 0 < F.extent i) {j : ℕ}
    (hj : j + 1 ≤ F.top) (y : F.Site (j + 1)) (c : Fin 4 → ℝ) :
    distFromPoint c (BlockAverages.refineSite y) = distFromPoint c y := by
  rw [blockRefine_eq_refineSite]
  exact distFromPoint_refineSite hL hs (Nat.le_succ j) hj y c
theorem abs_distFromPoint_read_sub_le (hL : Odd F.blockSide) (hs : ∀ i, 0 < F.extent i) {j : ℕ}
    (hj : j + 1 ≤ F.top) (y : F.Site (j + 1)) (c : Fin 4 → ℝ) (k l : Fin 4) (h : Fin 4 → ℤ)
    (hh : h ∈ BlockAverages.centredCube F.blockSide) (m m' : ℕ) (hm : m ∈ Finset.range F.blockSide)
    (hm' : m' ∈ Finset.range F.blockSide) :
    |distFromPoint c (BlockAverages.refineSite y + BlockAverages.siteOfCoords j h + axisOffset j k (m : ℤ) +
        axisOffset j l (m' : ℤ)) - distFromPoint c y| ≤
      3 * (F.blockSide : ℝ) / (F.blockSide : ℝ) ^ (F.top - j) := by
  obtain ⟨v, hv, hb⟩ := exists_read_offset hL y k l h hh m m' hm hm'
  have hM : (0 : ℝ) < (F.blockSide : ℝ) ^ (F.top - j) := by
    have : 0 < F.blockSide := hL.pos
    positivity
  have hbd : ∀ (s : Fin 4 → ℤ), (∀ i, |s i| ≤ 3 * (F.blockSide : ℤ)) →
      ∀ i, |(s i : ℝ)| / (F.blockSide : ℝ) ^ (F.top - j) ≤
        3 * (F.blockSide : ℝ) / (F.blockSide : ℝ) ^ (F.top - j) := by
    intro s hs' i
    refine div_le_div_of_nonneg_right ?_ hM.le
    have : ((|s i| : ℤ) : ℝ) ≤ ((3 * (F.blockSide : ℤ) : ℤ) : ℝ) := by exact_mod_cast hs' i
    push_cast at this
    exact this
  rw [hv, ← distFromPoint_blockRefine hL hs hj y c, abs_le]
  have a1 := distFromPoint_add_le hL hs (BlockAverages.refineSite y) v c _ (hbd v hb)
  have e : BlockAverages.refineSite y = BlockAverages.refineSite y + BlockAverages.siteOfCoords j v +
      BlockAverages.siteOfCoords j (-v) := by
    rw [siteOfCoords_neg, add_neg_cancel_right]
  have a2 := distFromPoint_add_le hL hs (BlockAverages.refineSite y + BlockAverages.siteOfCoords j v) (-v) c _
    (hbd (-v) fun i => by simpa using hb i)
  rw [← e] at a2
  constructor <;> linarith
def readReach (F : BlockAverages.BlockFrame) (j : ℕ) : ℝ :=
  4 / (F.blockSide : ℝ) * (1 - (1 / (F.blockSide : ℝ)) ^ (F.depth - j))
theorem readReach_nonneg (hL4 : 4 ≤ F.blockSide) (j : ℕ) : 0 ≤ readReach F j := by
  have h : (4 : ℝ) ≤ F.blockSide := by exact_mod_cast hL4
  have h0 : (0 : ℝ) < F.blockSide := by linarith
  unfold readReach
  have : (1 / (F.blockSide : ℝ)) ^ (F.depth - j) ≤ 1 := pow_le_one₀ (by positivity) (by
    rw [div_le_one h0]
    linarith)
  have : 0 ≤ 1 - (1 / (F.blockSide : ℝ)) ^ (F.depth - j) := by linarith
  positivity
theorem readReach_le (hL4 : 4 ≤ F.blockSide) (j : ℕ) : readReach F j ≤ 4 / (F.blockSide : ℝ) := by
  have h : (4 : ℝ) ≤ F.blockSide := by exact_mod_cast hL4
  unfold readReach
  have : 0 ≤ (1 / (F.blockSide : ℝ)) ^ (F.depth - j) := by positivity
  have h4 : 0 ≤ 4 / (F.blockSide : ℝ) := by positivity
  nlinarith
theorem readReach_succ_add_le (hL4 : 4 ≤ F.blockSide) {j : ℕ} (hj : j + 1 ≤ F.depth) :
    readReach F (j + 1) + 3 * (F.blockSide : ℝ) / (F.blockSide : ℝ) ^ (F.top - j) ≤ readReach F j := by
  have h : (4 : ℝ) ≤ F.blockSide := by exact_mod_cast hL4
  have h0 : (0 : ℝ) < F.blockSide := by linarith
  have e1 : F.depth - j = (F.depth - (j + 1)) + 1 := by omega
  have e2 : F.top - j = (F.depth - (j + 1)) + 2 := by
    unfold BlockAverages.BlockFrame.top
    omega
  set q := F.depth - (j + 1) with hq
  unfold readReach
  rw [e1, e2, ← hq]
  have e3 : 3 * (F.blockSide : ℝ) / (F.blockSide : ℝ) ^ (q + 2) =
      3 / (F.blockSide : ℝ) * (1 / (F.blockSide : ℝ)) ^ q := by
    rw [pow_add, one_div, inv_pow]
    field_simp
  rw [e3, pow_succ]
  set Q := (1 / (F.blockSide : ℝ)) ^ q
  have e4 : 4 / (F.blockSide : ℝ) * (1 - Q * (1 / (F.blockSide : ℝ))) -
      (4 / (F.blockSide : ℝ) * (1 - Q) + 3 / (F.blockSide : ℝ) * Q) =
      Q / (F.blockSide : ℝ) * (1 - 4 / (F.blockSide : ℝ)) := by
    field_simp
    ring
  have h1 : 0 ≤ Q / (F.blockSide : ℝ) * (1 - 4 / (F.blockSide : ℝ)) := by
    have : 4 / (F.blockSide : ℝ) ≤ 1 := by
      rw [div_le_one h0]
      exact h
    have : 0 ≤ 1 - 4 / (F.blockSide : ℝ) := by linarith
    positivity
  linarith
open Classical in
def nearWeight (c : Fin 4 → ℝ) (r : ℝ) (j : ℕ) (x : F.Site j) : ℝ :=
  if j ≤ F.depth ∧ distFromPoint c x ≤ r + readReach F j then 1 else 0
open Classical in
def farWeight (c : Fin 4 → ℝ) (r : ℝ) (j : ℕ) (x : F.Site j) : ℝ :=
  if j ≤ F.depth ∧ r - readReach F j < distFromPoint c x then 1 else 0
theorem isReadMonotone_nearWeight (hL : Odd F.blockSide) (hs : ∀ i, 0 < F.extent i) (hL4 : 4 ≤ F.blockSide)
    (c : Fin 4 → ℝ) (r : ℝ) : IsReadMonotone (nearWeight (F := F) c r) := by
  intro j hj y k l h hh m hm m' hm'
  by_cases hc : j + 1 ≤ F.depth ∧ distFromPoint c y ≤ r + readReach F (j + 1)
  · have hd := (abs_le.1 (abs_distFromPoint_read_sub_le hL hs hj y c k l h hh m m' hm hm')).2
    have hst := readReach_succ_add_le hL4 hc.1
    have : nearWeight c r j (BlockAverages.refineSite y + BlockAverages.siteOfCoords j h +
        axisOffset j k (m : ℤ) + axisOffset j l (m' : ℤ)) = 1 := by
      unfold nearWeight
      rw [if_pos]
      exact ⟨by omega, by linarith [hc.2]⟩
    rw [this]
    unfold nearWeight
    rw [if_pos hc]
  · have : nearWeight c r (j + 1) y = 0 := by
      unfold nearWeight
      rw [if_neg hc]
    rw [this]
    simp only [ne_eq, OfNat.ofNat_ne_zero, not_false_eq_true, zero_pow]
    exact sq_nonneg _
theorem isReadMonotone_farWeight (hL : Odd F.blockSide) (hs : ∀ i, 0 < F.extent i) (hL4 : 4 ≤ F.blockSide)
    (c : Fin 4 → ℝ) (r : ℝ) : IsReadMonotone (farWeight (F := F) c r) := by
  intro j hj y k l h hh m hm m' hm'
  by_cases hc : j + 1 ≤ F.depth ∧ r - readReach F (j + 1) < distFromPoint c y
  · have hd := (abs_le.1 (abs_distFromPoint_read_sub_le hL hs hj y c k l h hh m m' hm hm')).1
    have hst := readReach_succ_add_le hL4 hc.1
    have : farWeight c r j (BlockAverages.refineSite y + BlockAverages.siteOfCoords j h +
        axisOffset j k (m : ℤ) + axisOffset j l (m' : ℤ)) = 1 := by
      unfold farWeight
      rw [if_pos]
      exact ⟨by omega, by linarith [hc.2]⟩
    rw [this]
    unfold farWeight
    rw [if_pos hc]
  · have : farWeight c r (j + 1) y = 0 := by
      unfold farWeight
      rw [if_neg hc]
    rw [this]
    simp only [ne_eq, OfNat.ofNat_ne_zero, not_false_eq_true, zero_pow]
    exact sq_nonneg _
def belowTopWeight (j : ℕ) (_x : F.Site j) : ℝ := if j ≤ F.depth then 1 else 0
theorem isReadMonotone_belowTopWeight : IsReadMonotone (belowTopWeight (F := F)) := by
  intro j hj y k l h hh m hm m' hm'
  unfold belowTopWeight
  by_cases hc : j + 1 ≤ F.depth
  · rw [if_pos hc, if_pos (by omega)]
  · rw [if_neg hc]
    simp only [ne_eq, OfNat.ofNat_ne_zero, not_false_eq_true, zero_pow]
    exact sq_nonneg _
end YangMills.Construction.ColdStepAtMirrorFrames
end
